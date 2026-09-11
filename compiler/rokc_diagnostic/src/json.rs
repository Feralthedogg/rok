//! A JSON value tree: diagnostics, the language server, the Jupyter
//! kernel and the doc search index all read and write through it.

use std::fmt;

/// A JSON string literal.
#[must_use]
fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Self>),
    Obj(Vec<(String, Self)>),
}

impl Json {
    /// `{"k": v, ...}`.
    pub fn obj<const N: usize>(fields: [(&str, Self); N]) -> Self {
        Self::Obj(fields.into_iter().map(|(k, v)| (k.to_owned(), v)).collect())
    }

    pub fn str(s: impl Into<String>) -> Self {
        Self::Str(s.into())
    }

    pub fn num(n: impl Into<f64>) -> Self {
        Self::Num(n.into())
    }

    /// Member `key` of an object, else `Null`.
    pub fn get(&self, key: &str) -> &Self {
        match self {
            Self::Obj(fields) => fields
                .iter()
                .find(|(k, _)| k == key)
                .map_or(&Self::Null, |(_, v)| v),
            _ => &Self::Null,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::Str(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_u32(&self) -> Option<u32> {
        match self {
            Self::Num(n) if *n >= 0.0 => Some(*n as u32),
            _ => None,
        }
    }

    pub fn parse(src: &str) -> Result<Self, String> {
        let mut p = Parser {
            s: src.as_bytes(),
            i: 0,
        };
        let v = p.value()?;
        p.ws();
        if p.i == p.s.len() {
            Ok(v)
        } else {
            Err(format!("trailing characters at {}", p.i))
        }
    }
}

impl fmt::Display for Json {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Null => f.write_str("null"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Num(n) if n.fract() == 0.0 && n.abs() < 1e15 => write!(f, "{}", *n as i64),
            Self::Num(n) => write!(f, "{n}"),
            Self::Str(s) => f.write_str(&json_str(s)),
            Self::Arr(items) => {
                f.write_str("[")?;
                for (i, v) in items.iter().enumerate() {
                    if i > 0 {
                        f.write_str(",")?;
                    }
                    write!(f, "{v}")?;
                }
                f.write_str("]")
            }
            Self::Obj(fields) => {
                f.write_str("{")?;
                for (i, (k, v)) in fields.iter().enumerate() {
                    if i > 0 {
                        f.write_str(",")?;
                    }
                    write!(f, "{}:{v}", json_str(k))?;
                }
                f.write_str("}")
            }
        }
    }
}

struct Parser<'a> {
    s: &'a [u8],
    i: usize,
}

impl Parser<'_> {
    fn ws(&mut self) {
        while self.s.get(self.i).is_some_and(u8::is_ascii_whitespace) {
            self.i += 1;
        }
    }

    fn eat(&mut self, lit: &str) -> bool {
        if self.s[self.i..].starts_with(lit.as_bytes()) {
            self.i += lit.len();
            true
        } else {
            false
        }
    }

    fn value(&mut self) -> Result<Json, String> {
        self.ws();
        let err = |i: usize| format!("unexpected input at {i}");
        match self.s.get(self.i).copied() {
            Some(b'{') => {
                self.i += 1;
                let mut fields = Vec::new();
                self.ws();
                if self.eat("}") {
                    return Ok(Json::Obj(fields));
                }
                loop {
                    self.ws();
                    let Json::Str(k) = self.value()? else {
                        return Err(err(self.i));
                    };
                    self.ws();
                    if !self.eat(":") {
                        return Err(err(self.i));
                    }
                    fields.push((k, self.value()?));
                    self.ws();
                    if self.eat("}") {
                        return Ok(Json::Obj(fields));
                    }
                    if !self.eat(",") {
                        return Err(err(self.i));
                    }
                }
            }
            Some(b'[') => {
                self.i += 1;
                let mut items = Vec::new();
                self.ws();
                if self.eat("]") {
                    return Ok(Json::Arr(items));
                }
                loop {
                    items.push(self.value()?);
                    self.ws();
                    if self.eat("]") {
                        return Ok(Json::Arr(items));
                    }
                    if !self.eat(",") {
                        return Err(err(self.i));
                    }
                }
            }
            Some(b'"') => self.string().map(Json::Str),
            _ if self.eat("null") => Ok(Json::Null),
            _ if self.eat("true") => Ok(Json::Bool(true)),
            _ if self.eat("false") => Ok(Json::Bool(false)),
            _ => {
                let start = self.i;
                while self
                    .s
                    .get(self.i)
                    .is_some_and(|c| c.is_ascii_digit() || b"+-.eE".contains(c))
                {
                    self.i += 1;
                }
                std::str::from_utf8(&self.s[start..self.i])
                    .ok()
                    .and_then(|t| t.parse().ok())
                    .map(Json::Num)
                    .ok_or_else(|| err(start))
            }
        }
    }

    fn hex4(&mut self) -> Result<u32, String> {
        let h = self
            .s
            .get(self.i..self.i + 4)
            .and_then(|h| std::str::from_utf8(h).ok())
            .and_then(|h| u32::from_str_radix(h, 16).ok())
            .ok_or("bad \\u escape")?;
        self.i += 4;
        Ok(h)
    }

    fn string(&mut self) -> Result<String, String> {
        self.i += 1;
        let mut out = Vec::new();
        loop {
            let c = *self.s.get(self.i).ok_or("unterminated string")?;
            self.i += 1;
            match c {
                b'"' => return String::from_utf8(out).map_err(|e| e.to_string()),
                b'\\' => {
                    let e = *self.s.get(self.i).ok_or("unterminated string")?;
                    self.i += 1;
                    let ch = match e {
                        b'n' => '\n',
                        b't' => '\t',
                        b'r' => '\r',
                        b'b' => '\u{8}',
                        b'f' => '\u{c}',
                        b'u' => {
                            let mut cp = self.hex4()?;
                            // A UTF-16 surrogate pair.
                            if (0xD800..0xDC00).contains(&cp) && self.eat("\\u") {
                                let lo = self.hex4()?;
                                cp = 0x10000
                                    + ((cp - 0xD800) << 10)
                                    + (lo.wrapping_sub(0xDC00) & 0x3FF);
                            }
                            char::from_u32(cp).unwrap_or('\u{FFFD}')
                        }
                        other => other as char,
                    };
                    let mut buf = [0; 4];
                    out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                }
                c => out.push(c),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Json;

    #[test]
    fn round_trip() {
        let src = r#"{"a":[1,2.5,true,null],"b":"x\"\né😀","c":{}}"#;
        let v = Json::parse(src).unwrap();
        assert_eq!(v.get("b").as_str(), Some("x\"\né😀"));
        assert_eq!(
            v.get("a"),
            &Json::Arr(vec![
                Json::num(1),
                Json::num(2.5),
                Json::Bool(true),
                Json::Null
            ])
        );
        assert_eq!(Json::parse(&v.to_string()).unwrap(), v);
        assert!(Json::parse("{\"a\":}").is_err());
    }
}
