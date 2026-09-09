//! f-string format spec (refs-lang 1.7.3, stdlib 2.10.7):
//! `[[fill]align][sign]['#']['0'][width]['.' precision][type]`.
//!
//! Shared source: the runtime parses dynamic (`${..}`) specs with it and
//! the compiler (`rokc_hir`, through `#[path]`) checks static ones, so
//! both read a spec the same way. `core` only.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FmtSpec {
    pub fill: char,
    /// `0` (none) or `<` `>` `^` `=`.
    pub align: u8,
    /// `0` (none) or `+` `-` ` `.
    pub sign: u8,
    pub alt: bool,
    pub zero: bool,
    pub width: Option<usize>,
    pub precision: Option<usize>,
    /// `0` (none) or one of `d b o x X f e E g s ?`.
    pub ty: u8,
}

const fn is_align(c: char) -> bool {
    matches!(c, '<' | '>' | '^' | '=')
}

/// The parsed spec, or what is wrong with it.
pub fn parse(text: &str) -> Result<FmtSpec, &'static str> {
    let mut spec = FmtSpec {
        fill: ' ',
        align: 0,
        sign: 0,
        alt: false,
        zero: false,
        width: None,
        precision: None,
        ty: 0,
    };
    let mut rest = text;
    let mut it = rest.chars();
    match (it.next(), it.next()) {
        (Some(f), Some(a)) if is_align(a) => {
            spec.fill = f;
            spec.align = a as u8;
            rest = &rest[f.len_utf8() + 1..];
        }
        (Some(a), _) if is_align(a) => {
            spec.align = a as u8;
            rest = &rest[1..];
        }
        _ => {}
    }
    let mut b = rest.as_bytes();
    if let [s @ (b'+' | b'-' | b' '), tail @ ..] = b {
        spec.sign = *s;
        b = tail;
    }
    if let [b'#', tail @ ..] = b {
        spec.alt = true;
        b = tail;
    }
    if let [b'0', tail @ ..] = b {
        spec.zero = true;
        b = tail;
    }
    spec.width = number(&mut b)?;
    if let [b'.', tail @ ..] = b {
        b = tail;
        spec.precision = Some(number(&mut b)?.ok_or("precision expected after `.`")?);
    }
    if let [t, tail @ ..] = b {
        if !matches!(
            t,
            b'd' | b'b' | b'o' | b'x' | b'X' | b'f' | b'e' | b'E' | b'g' | b's' | b'?'
        ) {
            return Err("unknown format type (expected one of `d b o x X f e E g s ?`)");
        }
        spec.ty = *t;
        b = tail;
    }
    if b.is_empty() {
        Ok(spec)
    } else {
        Err("malformed spec (`[[fill]align][sign][#][0][width][.precision][type]`)")
    }
}

fn number(b: &mut &[u8]) -> Result<Option<usize>, &'static str> {
    let n = b.iter().take_while(|c| c.is_ascii_digit()).count();
    if n == 0 {
        return Ok(None);
    }
    let mut v: usize = 0;
    for &c in &b[..n] {
        v = v
            .checked_mul(10)
            .and_then(|v| v.checked_add(usize::from(c - b'0')))
            .ok_or("width / precision too large")?;
    }
    *b = &b[n..];
    Ok(Some(v))
}
