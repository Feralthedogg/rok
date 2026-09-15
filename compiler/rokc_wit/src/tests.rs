use std::path::Path;

use crate::abi::{self, Flat};
use crate::parse::{Prim, parse_file};
use crate::resolve::{FnKind, Resolve, Type, TypeKind};

const FS: &str = r"
package my:fs@1.0.0;

/// Docs are comments.
interface types {
    type size = u64;
    record stat { size: size, mtime: u64, is-dir: bool }
    variant error { not-found, permission-denied, io-error(string) }
    enum kind { file, dir }
    flags mode { read, write, %exec }
    resource file {
        constructor(path: string);
        read: func(buf-size: u32) -> result<list<u8>, error>;
        open: static func(path: string) -> file;
    }
    @unstable(feature = later)
    hidden: func();
    @since(version = 1.0.0)
    walk: func(dirs: list<tuple<string, option<kind>>>) -> option<stat>;
}

interface api {
    use types.{file, error as fs-error};
    open: func(path: string, m: borrow<file>) -> result<file, fs-error>;
}

world app {
    import api;
    export run: func(args: list<string>) -> result;
}
";

fn resolve(src: &str) -> Resolve {
    let f = parse_file(Path::new("fs.wit"), src).unwrap();
    Resolve::new(vec![(f, src.to_owned())]).unwrap()
}

fn ty(r: &Resolve, name: &str) -> Type {
    let id = r.types.iter().position(|t| t.name == name).unwrap();
    Type::Id(id)
}

#[test]
fn parses_and_resolves_every_kind() {
    let r = resolve(FS);
    assert_eq!(r.packages[0].name.to_string(), "my:fs@1.0.0");
    let types = &r.interfaces[0];
    let names: Vec<&str> = types.types.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["size", "stat", "error", "kind", "mode", "file"]);
    // `hidden` is unstable: left out. The resource's functions are the
    // interface's, `self` first for a method.
    let funcs: Vec<String> = types.funcs.iter().map(|f| f.wit_name(&r)).collect();
    assert_eq!(
        funcs,
        [
            "[constructor]file",
            "[method]file.read",
            "[static]file.open",
            "walk"
        ]
    );
    assert!(matches!(types.funcs[1].kind, FnKind::Method(_)));
    assert_eq!(types.funcs[1].params[0].0, "self");
    let TypeKind::Flags(f) = &r.types[r.dealias(ty(&r, "mode").id())].kind else {
        panic!()
    };
    assert_eq!(f, &["read", "write", "exec"]);
    // `use .. as`: an alias of the used type.
    let api = &r.interfaces[1];
    let open = &api.funcs[0];
    let Some(Type::Result(Some(ok), Some(err))) = &open.result else {
        panic!()
    };
    assert!(matches!(**ok, Type::Id(_)));
    let Type::Id(e) = **err else { panic!() };
    assert_eq!(r.types[r.dealias(e)].name, "error");
    assert_eq!(r.iface_key(1), "my:fs/api@1.0.0");
    assert_eq!(r.worlds[0].imports.len(), 1);
    assert_eq!(r.worlds[0].exports.len(), 1);
}

impl Type {
    const fn id(&self) -> usize {
        match self {
            Self::Id(i) | Self::Own(i) | Self::Borrow(i) => *i,
            _ => panic!(),
        }
    }
}

#[test]
fn canonical_layout() {
    let r = resolve(FS);
    // stat: u64, u64, bool → 24 bytes, align 8.
    assert_eq!(
        (
            abi::size(&r, &ty(&r, "stat")),
            abi::align(&r, &ty(&r, "stat"))
        ),
        (24, 8)
    );
    // error: u8 discriminant, string payload at 4 → 12 bytes.
    assert_eq!(abi::size(&r, &ty(&r, "error")), 12);
    assert_eq!(
        abi::flatten(&r, &ty(&r, "error")),
        [Flat::I32, Flat::I32, Flat::I32]
    );
    assert_eq!(abi::size(&r, &ty(&r, "mode")), 1);
    // option<stat>: discriminant then the record at 8.
    let opt = Type::Option(Box::new(ty(&r, "stat")));
    assert_eq!(abi::size(&r, &opt), 32);
    assert_eq!(
        abi::flatten(&r, &opt),
        [Flat::I32, Flat::I64, Flat::I64, Flat::I32]
    );
    // Joined slots: f32 with u32 is i32, with u64 is i64.
    let v = Type::Result(
        Some(Box::new(Type::Prim(Prim::F32))),
        Some(Box::new(Type::Prim(Prim::U64))),
    );
    assert_eq!(abi::flatten(&r, &v), [Flat::I32, Flat::I64]);
}

#[test]
fn errors_name_the_place() {
    let e = parse_file(
        Path::new("x.wit"),
        "package a:b;\ninterface i {\n  f: func(x: u32) -> ;\n}\n",
    )
    .unwrap_err();
    assert_eq!((e.line, e.col), (3, 22));
    assert!(e.msg.contains("expected a type"), "{}", e.msg);
    let src = "package a:b;\ninterface i { f: func(x: nope); }\n";
    let f = parse_file(Path::new("x.wit"), src).unwrap();
    let e = Resolve::new(vec![(f, src.to_owned())]).unwrap_err();
    assert!(e.msg.contains("no type `nope`"), "{}", e.msg);
}
