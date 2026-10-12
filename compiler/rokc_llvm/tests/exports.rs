//! rokc.exe's exports (`build/exports.rs`): COFF archive symbols and the
//! module definition file.

#[path = "../build/exports.rs"]
mod exports;

/// A COFF object (`bigobj`: the /bigobj form) with sections `.text`
/// (plain), `.text$a` (COMDAT, any), `.text$n` (COMDAT, no duplicates)
/// and symbols (name, section, is function, class).
fn object(bigobj: bool, syms: &[(&str, i32, bool, u8)]) -> Vec<u8> {
    let sections: [(&[u8], u32, u8); 3] = [
        (b".text", 0x6000_0020, 0),
        (b".text$a", 0x6000_1020, 2),
        (b".text$n", 0x6000_1020, 1),
    ];
    let (header, symsize) = if bigobj { (56, 20) } else { (20, 18) };
    let mut strtab = vec![0u8; 4];
    let mut table = Vec::new();
    let mut nsyms = 0u32;
    let mut sym = |name: &[u8], value: u32, section: i32, ty: u16, class: u8, aux: Option<u8>| {
        if name.len() <= 8 {
            let mut n = [0u8; 8];
            n[..name.len()].copy_from_slice(name);
            table.extend(n);
        } else {
            table.extend([0u8; 4]);
            table.extend((strtab.len() as u32).to_le_bytes());
            strtab.extend(name);
            strtab.push(0);
        }
        table.extend(value.to_le_bytes());
        if bigobj {
            table.extend(section.to_le_bytes());
        } else {
            table.extend((section as i16).to_le_bytes());
        }
        table.extend(ty.to_le_bytes());
        table.extend([class, u8::from(aux.is_some())]);
        nsyms += 1;
        if let Some(selection) = aux {
            let mut rec = vec![0u8; symsize];
            rec[14] = selection;
            table.extend(rec);
            nsyms += 1;
        }
    };
    for (i, (name, _, selection)) in sections.iter().enumerate() {
        sym(name, 0, i as i32 + 1, 0, 3, Some(*selection));
    }
    for &(name, section, function, class) in syms {
        let ty = if function { 0x20 } else { 0 };
        sym(name.as_bytes(), 0, section, ty, class, None);
    }
    let len = strtab.len() as u32;
    strtab[..4].copy_from_slice(&len.to_le_bytes());
    let symtab = (header + 40 * sections.len()) as u32;
    let mut d = Vec::new();
    if bigobj {
        d.extend([0, 0, 0xff, 0xff, 2, 0, 0x64, 0x86, 0, 0, 0, 0]);
        d.extend([
            0xc7, 0xa1, 0xba, 0xd1, 0xee, 0xba, 0xa9, 0x4b, 0xaf, 0x20, 0xfa, 0xf6, 0x6a, 0xa4,
            0xdc, 0xb8,
        ]);
        d.extend([0u8; 16]);
        d.extend((sections.len() as u32).to_le_bytes());
        d.extend(symtab.to_le_bytes());
        d.extend(nsyms.to_le_bytes());
    } else {
        d.extend(0xaa64u16.to_le_bytes());
        d.extend((sections.len() as u16).to_le_bytes());
        d.extend([0u8; 4]);
        d.extend(symtab.to_le_bytes());
        d.extend(nsyms.to_le_bytes());
        d.extend([0u8; 4]);
    }
    for (name, flags, _) in sections {
        let mut n = [0u8; 8];
        n[..name.len()].copy_from_slice(name);
        d.extend(n);
        d.extend([0u8; 28]);
        d.extend(flags.to_le_bytes());
    }
    d.extend(table);
    d.extend(strtab);
    d
}

/// An archive of a linker member, `objs` and a short import member.
fn archive(objs: &[Vec<u8>]) -> Vec<u8> {
    let mut a = b"!<arch>\n".to_vec();
    let mut member = |name: &str, data: &[u8]| {
        a.extend(
            format!(
                "{name:<16}{:<12}{:<6}{:<6}{:<8}{:<10}`\n",
                0,
                0,
                0,
                0,
                data.len()
            )
            .bytes(),
        );
        a.extend(data);
        if data.len() % 2 == 1 {
            a.push(b'\n');
        }
    };
    member("/", &[0, 0, 0, 0, 1]);
    for (i, o) in objs.iter().enumerate() {
        member(&format!("o{i}.obj/"), o);
    }
    member("x.dll/", &[0, 0, 0xff, 0xff, 0, 0, 0x64, 0x86, 0, 0, 0, 0]);
    a
}

#[test]
fn coff_members_tell_strong_weak_data_and_undefined() {
    let syms = [
        ("?f@llvm@@YAHH@Z", 1, true, 2),
        ("?counter@llvm@@3HA", 1, false, 2),
        ("?inline_template_instance@llvm@@YAHH@Z", 2, true, 2),
        ("?gy@llvm@@YAHH@Z", 3, true, 2),
        ("?local@@YAHH@Z", 1, true, 3),
        ("?undefined@@YAHH@Z", 0, true, 2),
        ("weak_alias", 0, true, 105),
    ];
    for bigobj in [false, true] {
        let ms = exports::coff_members(&archive(&[object(bigobj, &syms)]));
        assert_eq!(ms.len(), 1, "bigobj {bigobj}");
        let m = &ms[0];
        assert_eq!(
            m.defs,
            ["?f@llvm@@YAHH@Z", "?counter@llvm@@3HA", "?gy@llvm@@YAHH@Z"]
        );
        assert_eq!(m.weak, ["?inline_template_instance@llvm@@YAHH@Z"]);
        assert_eq!(m.data, ["?counter@llvm@@3HA"]);
        assert_eq!(m.undefs, ["?undefined@@YAHH@Z"]);
    }
}

#[test]
fn the_def_file_filters_like_extract_symbols() {
    let s = |n: &str, data: bool| (n.to_owned(), data);
    let syms = [
        s("?f@llvm@@YAHH@Z", false),
        s(
            "?id@?$TypeIDResolver@VArithDialect@arith@mlir@@X@detail@mlir@@0VSelfOwningTypeID@3@A",
            true,
        ),
        s("??_GPass@mlir@@UEAAPEAXI@Z", false),
        s("??_EPass@mlir@@UEAAPEAXI@Z", false),
        s("??_C@_04IAIHIHKK@$$J0?$AA@", true),
        s("?helper@?A0x1b2c3d4e@mlir@@YAXXZ", false),
        s("?h@?A@mlir@@YAXXZ", false),
        s("?Add@mlir@@YAXXZ", false),
        s("LLVMCantFail", false),
    ];
    assert_eq!(
        exports::def_file(&syms, false).unwrap(),
        "NAME rokc.exe\nEXPORTS\n  ?Add@mlir@@YAXXZ\n  ?f@llvm@@YAHH@Z\n  \
         ?id@?$TypeIDResolver@VArithDialect@arith@mlir@@X@detail@mlir@@0VSelfOwningTypeID@3@A DATA\n  \
         LLVMCantFail\n"
    );
    let x86 = [
        s("_LLVMCantFail", false),
        s("_f@8", false),
        s("@g@4", false),
    ];
    assert_eq!(
        exports::def_file(&x86, true).unwrap(),
        "NAME rokc.exe\nEXPORTS\n  LLVMCantFail\n  f\n  g\n"
    );
    let many: Vec<_> = (0..=exports::MAX_EXPORTS)
        .map(|i| (format!("f{i}"), false))
        .collect();
    assert!(exports::def_file(&many, false).is_err());
}
