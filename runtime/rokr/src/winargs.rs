//! The Windows command line: split as the MSVC CRT does (`argv` from
//! `GetCommandLineW`) and quoted for it (`CreateProcessW`). Plain code,
//! built on every host for its tests.

use rokr_common::wtf8::{MBuf, Wide, narrow};

/// The parsed command line: `count` WTF-8 arguments, each followed by a
/// NUL, built once and never freed.
pub struct Args {
    pub count: usize,
    pub bytes: MBuf<u8>,
}

/// Split a command line the way the MSVC CRT does: `argv[0]` up to the
/// first blank (or inside its quotes, taken literally); then blanks
/// separate arguments, `"` toggles quoting (`""` inside quotes is a
/// literal `"`), `2n` backslashes before a `"` are `n` backslashes,
/// `2n + 1` are `n` and a literal `"`; other backslashes are literal.
pub fn parse_command_line(line: &[u16]) -> Args {
    let mut out = Args {
        count: 0,
        bytes: MBuf::new(),
    };
    let (q, bs) = (u16::from(b'"'), u16::from(b'\\'));
    let blank = |u: u16| u == u16::from(b' ') || u == u16::from(b'\t');
    let mut cur = Wide::new();
    let mut i = 0;
    // argv[0]
    if line.first() == Some(&q) {
        i = 1;
        while i < line.len() && line[i] != q {
            cur.push(line[i]);
            i += 1;
        }
        i += 1;
    } else {
        while i < line.len() && !blank(line[i]) {
            cur.push(line[i]);
            i += 1;
        }
    }
    let finish = |cur: &mut Wide, out: &mut Args| {
        out.bytes.extend(narrow(cur.as_slice()).as_slice());
        out.bytes.push(0);
        out.count += 1;
        cur.truncate(0);
    };
    finish(&mut cur, &mut out);
    loop {
        while i < line.len() && blank(line[i]) {
            i += 1;
        }
        if i >= line.len() {
            return out;
        }
        let mut quoted = false;
        while i < line.len() && (quoted || !blank(line[i])) {
            let u = line[i];
            if u == bs {
                let mut n = 0;
                while i < line.len() && line[i] == bs {
                    n += 1;
                    i += 1;
                }
                if i < line.len() && line[i] == q {
                    for _ in 0..n / 2 {
                        cur.push(bs);
                    }
                    if n % 2 == 1 {
                        cur.push(q);
                        i += 1;
                    }
                } else {
                    for _ in 0..n {
                        cur.push(bs);
                    }
                }
            } else if u == q {
                if quoted && line.get(i + 1) == Some(&q) {
                    cur.push(q);
                    i += 2;
                } else {
                    quoted = !quoted;
                    i += 1;
                }
            } else {
                cur.push(u);
                i += 1;
            }
        }
        finish(&mut cur, &mut out);
    }
}

/// Append `arg` to the command line `cmd`, quoted for the MSVC CRT
/// parser (see [`parse_command_line`]).
pub fn push_arg(cmd: &mut Wide, arg: &[u16]) {
    let (q, bs) = (u16::from(b'"'), u16::from(b'\\'));
    if !cmd.is_empty() {
        cmd.push(u16::from(b' '));
    }
    let plain = !arg.is_empty()
        && !arg.iter().any(|&u| {
            u == q
                || u == u16::from(b' ')
                || u == u16::from(b'\t')
                || u == u16::from(b'\n')
                || u == 0x0B
        });
    if plain {
        cmd.extend(arg);
        return;
    }
    cmd.push(q);
    let mut backslashes = 0;
    for &u in arg {
        if u == bs {
            backslashes += 1;
        } else {
            if u == q {
                for _ in 0..=backslashes {
                    cmd.push(bs);
                }
            }
            backslashes = 0;
        }
        cmd.push(u);
    }
    for _ in 0..backslashes {
        cmd.push(bs);
    }
    cmd.push(q);
}

#[cfg(test)]
mod tests {
    use super::*;
    use rokr_common::wtf8::wide;

    fn parse(s: &str) -> MBuf<u8> {
        let mut w = Wide::new();
        for u in s.encode_utf16() {
            w.push(u);
        }
        parse_command_line(w.as_slice()).bytes
    }

    #[test]
    fn command_line_follows_the_crt() {
        assert_eq!(
            parse(r#""C:\a b\p.exe" x "y z""#).as_slice(),
            b"C:\\a b\\p.exe\0x\0y z\0"
        );
        assert_eq!(
            parse(r#"p a\\\"b "c\\" d\e"#).as_slice(),
            b"p\0a\\\"b\0c\\\0d\\e\0"
        );
        assert_eq!(parse(r#"p "a""b" """#).as_slice(), b"p\0a\"b\0\0");
        assert_eq!(parse("p\t  q  ").as_slice(), b"p\0q\0");
    }

    #[test]
    fn quoting_round_trips() {
        let args = ["p", "a b", "c\"d", "e\\", "", "f\\\"g\\\\", "tab\there"];
        let mut cmd = Wide::new();
        for a in args {
            push_arg(&mut cmd, wide(a.as_bytes()).as_slice());
        }
        let back = parse_command_line(cmd.as_slice());
        let mut want = MBuf::new();
        for a in args {
            want.extend(a.as_bytes());
            want.push(0);
        }
        assert_eq!(back.count, args.len());
        assert_eq!(back.bytes.as_slice(), want.as_slice());
    }
}
