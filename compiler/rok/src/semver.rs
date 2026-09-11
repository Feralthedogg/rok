//! Semantic versions (`1.2.3`, `1.0.0-rc.1+build`) and requirements
//! (`^1.2`, `~1.2.3`, `=1.0`, `>=1.2, <2`, `1.*`, `*`; a bare version is
//! `^`), with Cargo's meaning.
//!
//! A pre-release version matches only a requirement that names a
//! pre-release of the same `major.minor.patch` (`^1.0.0-rc.1` matches
//! `1.0.0-rc.2`, `^1.0` does not).

use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Version {
    pub major: u64,
    pub minor: u64,
    pub patch: u64,
    /// Dot-separated pre-release identifiers (empty: a release).
    pub pre: Vec<String>,
}

fn num(s: &str, what: &str) -> Result<u64, String> {
    // No leading zeros, like semver (`01` is not a version part).
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) || (s.len() > 1 && s.starts_with('0'))
    {
        return Err(format!("`{s}` is not a valid {what}"));
    }
    s.parse().map_err(|_| format!("`{s}` is too large"))
}

fn ident(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
}

/// `pre` and build of `x.y.z-pre+build`: the dotted part before `-`, the
/// pre-release identifiers.
fn split_pre(s: &str) -> Result<(&str, Vec<String>), String> {
    let s = match s.split_once('+') {
        Some((v, b)) if b.split('.').all(ident) => v,
        Some(_) => return Err(format!("bad build metadata in `{s}`")),
        None => s,
    };
    match s.split_once('-') {
        Some((v, p)) if p.split('.').all(ident) => {
            Ok((v, p.split('.').map(str::to_owned).collect()))
        }
        Some(_) => Err(format!("bad pre-release in `{s}`")),
        None => Ok((s, Vec::new())),
    }
}

impl Version {
    pub fn parse(s: &str) -> Result<Self, String> {
        let bad = |e: String| format!("`{s}` is not a version (major.minor.patch): {e}");
        let (core, pre) = split_pre(s.trim()).map_err(bad)?;
        let parts: Vec<&str> = core.split('.').collect();
        let [a, b, c] = parts.as_slice() else {
            return Err(bad("it needs three numbers".into()));
        };
        Ok(Self {
            major: num(a, "major version").map_err(bad)?,
            minor: num(b, "minor version").map_err(bad)?,
            patch: num(c, "patch version").map_err(bad)?,
            pre,
        })
    }

    const fn new(major: u64, minor: u64, patch: u64) -> Self {
        Self {
            major,
            minor,
            patch,
            pre: Vec::new(),
        }
    }

    const fn triple(&self) -> (u64, u64, u64) {
        (self.major, self.minor, self.patch)
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;
        if !self.pre.is_empty() {
            write!(f, "-{}", self.pre.join("."))?;
        }
        Ok(())
    }
}

impl Ord for Version {
    fn cmp(&self, o: &Self) -> Ordering {
        self.triple().cmp(&o.triple()).then_with(|| {
            match (self.pre.is_empty(), o.pre.is_empty()) {
                (true, true) => Ordering::Equal,
                // A release is above its pre-releases.
                (true, false) => Ordering::Greater,
                (false, true) => Ordering::Less,
                (false, false) => {
                    for (a, b) in self.pre.iter().zip(&o.pre) {
                        let c = match (a.parse::<u64>(), b.parse::<u64>()) {
                            (Ok(x), Ok(y)) => x.cmp(&y),
                            (Ok(_), Err(_)) => Ordering::Less,
                            (Err(_), Ok(_)) => Ordering::Greater,
                            (Err(_), Err(_)) => a.cmp(b),
                        };
                        if c != Ordering::Equal {
                            return c;
                        }
                    }
                    self.pre.len().cmp(&o.pre.len())
                }
            }
        })
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Ge,
    Gt,
    Lt,
    Le,
}

/// A requirement: comparators that must all hold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Req {
    /// Lowered to bounds.
    bounds: Vec<(Op, Version)>,
    /// The `major.minor.patch` of comparators written with a pre-release.
    pre_ok: Vec<(u64, u64, u64)>,
}

impl Req {
    pub fn parse(s: &str) -> Result<Self, String> {
        let mut req = Self {
            bounds: Vec::new(),
            pre_ok: Vec::new(),
        };
        for c in s.split(',') {
            req.comparator(c.trim())
                .map_err(|e| format!("`{s}` is not a version requirement: {e}"))?;
        }
        Ok(req)
    }

    fn comparator(&mut self, c: &str) -> Result<(), String> {
        let (op, rest) = ["<=", ">=", "=", "<", ">", "^", "~"]
            .iter()
            .find_map(|op| c.strip_prefix(op).map(|r| (*op, r.trim_start())))
            .unwrap_or(("^", c));
        if rest.is_empty() {
            return Err("a comparator needs a version".into());
        }
        let (core, pre) = split_pre(rest)?;
        let mut parts = core.split('.');
        let mut part = |what| -> Result<Option<u64>, String> {
            match parts.next() {
                None | Some("*" | "x" | "X") => Ok(None),
                Some(p) => num(p, what).map(Some),
            }
        };
        let (major, minor, patch) = (part("major")?, part("minor")?, part("patch")?);
        if parts.next().is_some() {
            return Err("more than three version numbers".into());
        }
        let wild = core.contains(['*', 'x', 'X']);
        if (minor.is_none() && patch.is_some()) || (wild && !matches!(op, "^" | "=")) {
            return Err(format!("`{c}` is not a comparator"));
        }
        // `1.*` / `1.2.*` mean `=1` / `=1.2`.
        let op = if wild { "=" } else { op };
        let Some(ma) = major else {
            return if core == "*" && pre.is_empty() && op == "=" {
                Ok(())
            } else {
                Err(format!("`{c}` is not a comparator"))
            };
        };
        if !pre.is_empty() {
            if minor.is_none() || patch.is_none() {
                return Err("a pre-release needs major.minor.patch".into());
            }
            self.pre_ok
                .push((ma, minor.unwrap_or(0), patch.unwrap_or(0)));
        }
        let low = Version {
            pre,
            ..Version::new(ma, minor.unwrap_or(0), patch.unwrap_or(0))
        };
        // The release above every `ma.mi.pa` with the unwritten parts
        // free (`1` -> `2.0.0`, `1.2` -> `1.3.0`); `None` when all three
        // are written.
        let next = match (minor, patch) {
            (None, _) => Some(Version::new(ma + 1, 0, 0)),
            (Some(mi), None) => Some(Version::new(ma, mi + 1, 0)),
            _ => None,
        };
        let b = &mut self.bounds;
        match (op, next) {
            ("=", Some(n)) => b.extend([(Op::Ge, low), (Op::Lt, n)]),
            ("=", None) => b.extend([(Op::Ge, low.clone()), (Op::Le, low)]),
            (">=", _) => b.push((Op::Ge, low)),
            (">", Some(n)) => b.push((Op::Ge, n)),
            (">", None) => b.push((Op::Gt, low)),
            ("<", _) => b.push((Op::Lt, low)),
            ("<=", Some(n)) => b.push((Op::Lt, n)),
            ("<=", None) => b.push((Op::Le, low)),
            ("~", _) => {
                let hi = match minor {
                    None => Version::new(ma + 1, 0, 0),
                    Some(mi) => Version::new(ma, mi + 1, 0),
                };
                b.extend([(Op::Ge, low), (Op::Lt, hi)]);
            }
            _ => {
                // `^`: the leftmost non-zero part may not change.
                let hi = match (ma, minor, patch) {
                    (0, Some(0), Some(pa)) => Version::new(0, 0, pa + 1),
                    (0, Some(mi), _) => Version::new(0, mi + 1, 0),
                    (0, None, _) => Version::new(1, 0, 0),
                    _ => Version::new(ma + 1, 0, 0),
                };
                b.extend([(Op::Ge, low), (Op::Lt, hi)]);
            }
        }
        Ok(())
    }

    pub fn matches(&self, v: &Version) -> bool {
        self.bounds.iter().all(|(op, b)| match op {
            Op::Ge => v >= b,
            Op::Gt => v > b,
            Op::Lt => v < b,
            Op::Le => v <= b,
        }) && (v.pre.is_empty() || self.pre_ok.contains(&v.triple()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(s: &str) -> Version {
        Version::parse(s).unwrap()
    }

    #[test]
    fn versions_order() {
        let mut vs: Vec<Version> = [
            "1.0.0",
            "1.0.0-rc.1",
            "1.0.0-alpha",
            "1.0.0-alpha.1",
            "1.0.0-alpha.beta",
            "1.0.0-beta.2",
            "1.0.0-beta.11",
            "0.9.10",
            "0.9.9",
            "10.0.0",
        ]
        .map(v)
        .to_vec();
        vs.sort();
        let s: Vec<String> = vs.iter().map(ToString::to_string).collect();
        assert_eq!(
            s,
            [
                "0.9.9",
                "0.9.10",
                "1.0.0-alpha",
                "1.0.0-alpha.1",
                "1.0.0-alpha.beta",
                "1.0.0-beta.2",
                "1.0.0-beta.11",
                "1.0.0-rc.1",
                "1.0.0",
                "10.0.0"
            ]
        );
        assert_eq!(v("1.2.3+build.5"), v("1.2.3"));
        for bad in [
            "1.2",
            "1.2.3.4",
            "01.2.3",
            "1.2.x",
            "a.b.c",
            "1.2.3-",
            "1.2.3-a..b",
            "",
        ] {
            assert!(Version::parse(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn requirements_match() {
        for (req, yes, no) in [
            (
                "^1.2.3",
                &["1.2.3", "1.9.0"][..],
                &["1.2.2", "2.0.0", "1.3.0-rc.1"][..],
            ),
            ("1.2", &["1.2.0", "1.99.1"], &["1.1.9", "2.0.0"]),
            ("^0.2.3", &["0.2.3", "0.2.9"], &["0.3.0", "0.2.2"]),
            ("^0.0.3", &["0.0.3"], &["0.0.4", "0.0.2"]),
            ("^0.0", &["0.0.7"], &["0.1.0"]),
            ("^0", &["0.9.9"], &["1.0.0"]),
            ("~1.2.3", &["1.2.3", "1.2.9"], &["1.3.0", "1.2.2"]),
            ("~1.2", &["1.2.0", "1.2.7"], &["1.3.0"]),
            ("~1", &["1.0.0", "1.9.0"], &["2.0.0"]),
            ("=1.2.3", &["1.2.3"], &["1.2.4", "1.2.2"]),
            ("=1.2", &["1.2.0", "1.2.5"], &["1.3.0"]),
            (">=1.2", &["1.2.0", "7.0.0"], &["1.1.9"]),
            (">1.2", &["1.3.0"], &["1.2.9"]),
            (">1.2.3", &["1.2.4"], &["1.2.3"]),
            ("<1.2", &["1.1.9"], &["1.2.0"]),
            ("<=1.2", &["1.2.9"], &["1.3.0"]),
            ("<=1.2.3", &["1.2.3"], &["1.2.4"]),
            (">= 1.2, < 1.5", &["1.4.9"], &["1.5.0", "1.1.0"]),
            ("*", &["0.0.1", "9.9.9"], &["1.0.0-rc.1"]),
            ("1.*", &["1.0.0", "1.9.9"], &["2.0.0"]),
            ("1.2.*", &["1.2.0", "1.2.9"], &["1.3.0"]),
            ("1.2.x", &["1.2.4"], &["1.3.0"]),
            (">1.0.0-rc.1", &["1.0.0-rc.2", "1.0.0"], &["1.0.0-rc.1"]),
            (
                "^1.0.0-rc.1",
                &["1.0.0-rc.1", "1.0.0-rc.2", "1.0.0", "1.5.0"],
                &["1.0.0-alpha", "1.1.0-rc.1"],
            ),
        ] {
            let r = Req::parse(req).unwrap();
            for y in yes {
                assert!(r.matches(&v(y)), "{req} should match {y}");
            }
            for n in no {
                assert!(!r.matches(&v(n)), "{req} should not match {n}");
            }
        }
        for bad in [
            "", "^", ">=x", "1.2.3.4", ">1.*", "~*", "1.*.3", "^1.2-rc", "1,", "abc",
        ] {
            assert!(Req::parse(bad).is_err(), "{bad}");
        }
    }
}
