//! Prebuilt dependencies (spec 902.3 / 904): each source `--extern` is
//! built once into `<deps dir>/lib<name>.a` + `<name>.rhir` and the build
//! goes on with the RHIR. A dependency is rebuilt when its fingerprint
//! changes; it sees the dependencies before it (its own, and the GC type
//! ids to start after), so `externs` come dependencies first.

use std::path::{Path, PathBuf};

use rokc_diagnostic::{print_rendered, render};

use crate::fresh::Fingerprint;
use crate::{BuildOptions, Session, rhir};

/// What dependency builds share with the build that needs them.
pub struct DepBuild<'a> {
    pub bootstrap: &'a [PathBuf],
    pub cfg: &'a [String],
    pub opts: &'a BuildOptions,
    /// `--target`: an LLVM triple; `None` is the host.
    pub target: Option<&'a str>,
    /// `target/[<triple>/]<profile>/deps`.
    pub dir: &'a Path,
    pub quiet: bool,
    /// The prebuilt standard library the build links (`prebuilt_std`).
    pub std: Option<&'a Path>,
}

impl DepBuild<'_> {
    /// `externs` with every source dependency (a `lib.rok`) replaced by
    /// its prebuilt `<name>.rhir`; dependency errors are reported.
    pub fn prebuild(
        &self,
        externs: &[(String, PathBuf)],
    ) -> Result<Vec<(String, PathBuf)>, String> {
        let mut out: Vec<(String, PathBuf)> = Vec::new();
        for (name, root) in externs {
            if root.extension().is_some_and(|e| e == "rhir") {
                out.push((name.clone(), root.clone()));
                continue;
            }
            std::fs::create_dir_all(self.dir)
                .map_err(|e| format!("cannot create {}: {e}", self.dir.display()))?;
            let archive = self.dir.join(format!("lib{name}.a"));
            let rhir = rhir::companions(&archive).0;
            let fp = self.fingerprint(name, root, &archive, &out);
            if let Some(warnings) = fp.fresh() {
                print_rendered(&warnings);
            } else {
                fp.clear();
                let (read, warnings) = self.build(name, root, &archive, &out)?;
                fp.save(&read, &warnings);
            }
            out.push((name.clone(), rhir));
        }
        Ok(out)
    }

    fn fingerprint(
        &self,
        name: &str,
        root: &Path,
        archive: &Path,
        before: &[(String, PathBuf)],
    ) -> Fingerprint {
        let mut words = vec![
            format!("{:?}", self.opts),
            format!("{:?}", self.target),
            name.to_owned(),
        ];
        words.extend(self.cfg.iter().cloned());
        let mut inputs = vec![root.parent().unwrap_or(root).to_path_buf()];
        let mut stamped = Vec::new();
        if let crate::Profile::Use(p) = &self.opts.profile {
            stamped.push(p.clone());
        }
        if let Some(std) = self.std {
            words.push(std.display().to_string());
            inputs.push(std.to_path_buf());
        }
        for b in self.bootstrap {
            words.push(b.display().to_string());
            inputs.push(b.parent().unwrap_or(b).to_path_buf());
        }
        for (n, p) in before {
            words.push(format!("{n}={}", p.display()));
            let (rhir, a) = rhir::companions(p);
            inputs.push(rhir);
            stamped.push(a);
        }
        let also = vec![rhir::companions(archive).0];
        Fingerprint::new(archive, also, &words, &inputs, &stamped)
            .kept_in(self.dir.join(format!("{name}.fp")))
    }

    /// Build one dependency; the files it read and its rendered warnings.
    fn build(
        &self,
        name: &str,
        root: &Path,
        archive: &Path,
        before: &[(String, PathBuf)],
    ) -> Result<(Vec<PathBuf>, String), String> {
        if !self.quiet {
            let dir = root.parent().unwrap_or(root);
            eprintln!("   Compiling {name} ({})", dir.display());
        }
        let mut s = Session::new();
        for b in self.bootstrap {
            s.add_bootstrap_file(b.clone());
        }
        for c in self.cfg {
            s.add_cfg(c.clone());
        }
        for (n, p) in before {
            s.add_extern(n.clone(), p.clone());
        }
        s.set_lib_name(Some(name.to_owned()));
        s.set_target(self.target);
        s.set_std_prebuilt(self.std.map(Path::to_path_buf));
        rokc_diagnostic::clear_files();
        let r = s.compile_file(root);
        let warnings: String = r.warnings.iter().map(render).collect();
        print_rendered(&warnings);
        let failed = || format!("could not build dependency `{name}`");
        if r.has_errors() {
            r.report_errors();
            return Err(failed());
        }
        r.archive(self.opts, archive, false).map_err(|d| {
            crate::report(&d);
            failed()
        })?;
        Ok((r.files, warnings))
    }
}
