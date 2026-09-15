#!/usr/bin/env python3
"""Link-only stub of a glibc shared library (the Zig model).

    glibc_stubs.py <lib.so.N> <out.s> <out.map>

Reads the exported symbols and their versions from a 32- or 64-bit
little-endian ELF shared library and writes an assembly file that
defines each one (`.symver` binds it to its version; objects keep their
size, aliases of one object share its storage) and the version script
that declares the versions. Assembled and linked with `-shared`, it is
an input lld links against as it would the real library. GLIBC_PRIVATE
symbols are left out.
"""

import struct
import sys

SHT_DYNSYM = 11
SHT_GNU_VERDEF = 0x6FFFFFFD
SHT_GNU_VERSYM = 0x6FFFFFFF
STT_OBJECT, STT_FUNC, STT_TLS = 1, 2, 6
STB_GLOBAL, STB_WEAK = 1, 2


def cstr(b, off):
    return b[off : b.index(b"\0", off)].decode()


def read(path):
    b = open(path, "rb").read()
    if b[:4] != b"\x7fELF" or b[4] not in (1, 2) or b[5] != 1:
        sys.exit(f"{path}: not a little-endian ELF")
    elf64 = b[4] == 2
    if elf64:
        shoff, = struct.unpack_from("<Q", b, 0x28)
        shentsize, shnum = struct.unpack_from("<HH", b, 0x3A)
        shdr, symsize = "<IIQQQQIIQQ", 24
    else:
        shoff, = struct.unpack_from("<I", b, 0x20)
        shentsize, shnum = struct.unpack_from("<HH", b, 0x2E)
        shdr, symsize = "<IIIIIIIIII", 16
    secs = [struct.unpack_from(shdr, b, shoff + i * shentsize) for i in range(shnum)]
    by_type = {s[1]: s for s in secs}
    dynsym, verdef, versym = (by_type[t] for t in (SHT_DYNSYM, SHT_GNU_VERDEF, SHT_GNU_VERSYM))
    strtab = secs[dynsym[6]][4]

    names = {}
    off = verdef[4]
    while True:
        _, flags, ndx, _, _, aux, nxt = struct.unpack_from("<HHHHIII", b, off)
        names[ndx] = (cstr(b, strtab + struct.unpack_from("<I", b, off + aux)[0]), flags & 1)
        if not nxt:
            break
        off += nxt

    syms = []
    for i in range(1, dynsym[5] // symsize):
        at = dynsym[4] + i * symsize
        if elf64:
            name, info, _, shndx, value, size = struct.unpack_from("<IBBHQQ", b, at)
        else:
            name, value, size, info, _, shndx = struct.unpack_from("<IIIBBH", b, at)
        ver, = struct.unpack_from("<H", b, versym[4] + i * 2)
        bind, typ = info >> 4, info & 0xF
        vname, base = names.get(ver & 0x7FFF, (None, 1))
        if shndx == 0 or bind not in (STB_GLOBAL, STB_WEAK) or base or vname == "GLIBC_PRIVATE":
            continue
        syms.append((cstr(b, strtab + name), vname, not ver & 0x8000, bind, typ, value, size))
    versions = [n for k, (n, base) in sorted(names.items()) if not base and n != "GLIBC_PRIVATE"]
    return syms, versions


def main():
    lib, out_s, out_map = sys.argv[1:]
    syms, versions = read(lib)
    s = []
    storage = {}
    for i, (name, ver, default, bind, typ, value, size) in enumerate(syms):
        label = f"s{i}"
        s.append(f".{'weak' if bind == STB_WEAK else 'globl'} {label}")
        if typ in (STT_OBJECT, STT_TLS):
            kind = "%tls_object" if typ == STT_TLS else "%object"
            sec = ".section .tbss,\"awT\",%nobits" if typ == STT_TLS else ".data"
            s += [f".type {label}, {kind}", f".size {label}, {size}"]
            first = storage.get((typ, value))
            if first is None:
                align = min(value & -value or 1, 64)
                storage[(typ, value)] = label
                s += [sec, f".balign {align}", f"{label}:", f".zero {max(size, 1)}"]
            else:
                s.append(f".set {label}, {first}")
        else:
            s += [".text", f".type {label}, %function", f"{label}:", "ret" if False else ".zero 1"]
        s.append(f".symver {label}, {name}{'@@' if default else '@'}{ver}, remove")
    open(out_s, "w").write("\n".join(s) + "\n")
    open(out_map, "w").write("".join(f"{v} {{ }};\n" for v in versions))


main()
