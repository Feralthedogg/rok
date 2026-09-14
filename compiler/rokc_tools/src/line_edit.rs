//! Line editing for the terminal REPL: raw-mode termios (Windows: console
//! modes with VT input), cursor keys,
//! a history kept in `$ROK_HOME/repl_history`, and the Emacs control
//! keys (`C-a` `C-e` `C-b` `C-f` `C-k` `C-u` `C-w` `C-d` `C-p` `C-n`
//! `C-l`). A line wider than the terminal is not re-wrapped.

use std::io::{Read, Write};
use std::path::PathBuf;

/// What one `read_line` got.
pub enum Input {
    Line(String),
    /// `C-c`: drop the line (and an open multi-line cell).
    Interrupt,
    /// `C-d` on an empty line, or the end of input.
    Eof,
}

/// History entries kept on disk.
const KEEP: usize = 1000;

pub struct Editor {
    history: Vec<String>,
    file: Option<PathBuf>,
}

impl Editor {
    /// An editor with the history of earlier sessions.
    pub fn new() -> Self {
        let file = rokc_core::rok_home().map(|h| h.join("repl_history"));
        let history = file
            .as_ref()
            .and_then(|f| std::fs::read_to_string(f).ok())
            .map(|s| s.lines().map(str::to_owned).collect())
            .unwrap_or_default();
        Self { history, file }
    }

    /// Remember `line` (and append it to the history file).
    pub fn add(&mut self, line: &str) {
        if line.trim().is_empty() || self.history.last().is_some_and(|l| l == line) {
            return;
        }
        self.history.push(line.to_owned());
        let Some(f) = &self.file else { return };
        if self.history.len() > KEEP * 2 {
            let drop = self.history.len() - KEEP;
            self.history.drain(..drop);
            let _ = std::fs::write(f, self.history.join("\n") + "\n");
        } else if let Some(dir) = f.parent() {
            let _ = std::fs::create_dir_all(dir);
            let _ = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(f)
                .and_then(|mut h| writeln!(h, "{line}"));
        }
    }

    /// Read one line after `prompt`; plain `read_line` when stdin is not
    /// a terminal raw mode can be set on.
    pub fn read_line(&self, prompt: &str) -> Input {
        let mut out = std::io::stdout();
        let _ = write!(out, "{prompt}");
        let _ = out.flush();
        let Some(_raw) = Raw::enter() else {
            let mut line = String::new();
            return match std::io::stdin().read_line(&mut line) {
                Ok(0) | Err(_) => Input::Eof,
                Ok(_) => Input::Line(line.trim_end_matches(['\n', '\r']).to_owned()),
            };
        };
        let mut st = State {
            buf: Vec::new(),
            pos: 0,
            hist: self.history.len(),
            draft: Vec::new(),
        };
        let mut stdin = std::io::stdin().lock();
        loop {
            let Some(b) = byte(&mut stdin) else {
                return Input::Eof;
            };
            match b {
                b'\r' | b'\n' => {
                    let _ = write!(out, "\r\n");
                    let _ = out.flush();
                    return Input::Line(st.buf.iter().collect());
                }
                3 => {
                    let _ = write!(out, "^C\r\n");
                    let _ = out.flush();
                    return Input::Interrupt;
                }
                4 if st.buf.is_empty() => {
                    let _ = write!(out, "\r\n");
                    return Input::Eof;
                }
                4 => st.delete(),
                1 => st.pos = 0,
                5 => st.pos = st.buf.len(),
                2 => st.pos = st.pos.saturating_sub(1),
                6 => st.pos = (st.pos + 1).min(st.buf.len()),
                11 => st.buf.truncate(st.pos),
                21 => {
                    st.buf.drain(..st.pos);
                    st.pos = 0;
                }
                23 => st.kill_word(),
                12 => {
                    let _ = write!(out, "\x1b[H\x1b[2J");
                }
                16 => st.recall(&self.history, -1),
                14 => st.recall(&self.history, 1),
                8 | 127 => {
                    if st.pos > 0 {
                        st.pos -= 1;
                        st.buf.remove(st.pos);
                    }
                }
                0x1b => match escape(&mut stdin).as_deref() {
                    Some("[A" | "OA") => st.recall(&self.history, -1),
                    Some("[B" | "OB") => st.recall(&self.history, 1),
                    Some("[C" | "OC") => st.pos = (st.pos + 1).min(st.buf.len()),
                    Some("[D" | "OD") => st.pos = st.pos.saturating_sub(1),
                    Some("[H" | "OH" | "[1~" | "[7~") => st.pos = 0,
                    Some("[F" | "OF" | "[4~" | "[8~") => st.pos = st.buf.len(),
                    Some("[3~") => st.delete(),
                    _ => {}
                },
                b if b < 0x20 => {}
                b => {
                    if let Some(c) = utf8(b, &mut stdin) {
                        st.buf.insert(st.pos, c);
                        st.pos += 1;
                    }
                }
            }
            st.draw(&mut out, prompt);
        }
    }
}

struct State {
    buf: Vec<char>,
    pos: usize,
    /// History index being shown (`len`: the line being typed).
    hist: usize,
    /// The line being typed, kept while browsing history.
    draft: Vec<char>,
}

impl State {
    fn delete(&mut self) {
        if self.pos < self.buf.len() {
            self.buf.remove(self.pos);
        }
    }

    fn kill_word(&mut self) {
        let mut i = self.pos;
        while i > 0 && self.buf[i - 1].is_whitespace() {
            i -= 1;
        }
        while i > 0 && !self.buf[i - 1].is_whitespace() {
            i -= 1;
        }
        self.buf.drain(i..self.pos);
        self.pos = i;
    }

    fn recall(&mut self, history: &[String], step: isize) {
        let Some(next) = self.hist.checked_add_signed(step) else {
            return;
        };
        if next > history.len() {
            return;
        }
        if self.hist == history.len() {
            self.draft = std::mem::take(&mut self.buf);
        }
        self.hist = next;
        self.buf = match history.get(next) {
            Some(h) => h.chars().collect(),
            None => self.draft.clone(),
        };
        self.pos = self.buf.len();
    }

    fn draw(&self, out: &mut impl Write, prompt: &str) {
        let line: String = self.buf.iter().collect();
        let col = prompt.chars().count() + self.pos;
        let _ = write!(out, "\r{prompt}{line}\x1b[K\r");
        if col > 0 {
            let _ = write!(out, "\x1b[{col}C");
        }
        let _ = out.flush();
    }
}

fn byte(r: &mut impl Read) -> Option<u8> {
    let mut b = [0u8; 1];
    loop {
        match r.read(&mut b) {
            Ok(1) => return Some(b[0]),
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            _ => return None,
        }
    }
}

/// The rest of an escape sequence after ESC: `[A`, `[3~`, `OH`, ..
fn escape(r: &mut impl Read) -> Option<String> {
    let first = byte(r)?;
    let mut s = String::from(char::from(first));
    if first != b'[' && first != b'O' {
        return Some(s);
    }
    loop {
        let b = byte(r)?;
        s.push(char::from(b));
        if b.is_ascii_alphabetic() || b == b'~' {
            return Some(s);
        }
    }
}

/// A char starting with byte `b` (reading its continuation bytes).
fn utf8(b: u8, r: &mut impl Read) -> Option<char> {
    let len = match b {
        0x00..=0x7f => 1,
        0xc0..=0xdf => 2,
        0xe0..=0xef => 3,
        0xf0..=0xf7 => 4,
        _ => return None,
    };
    let mut bytes = vec![b];
    for _ in 1..len {
        bytes.push(byte(r)?);
    }
    std::str::from_utf8(&bytes).ok()?.chars().next()
}

/// Raw mode on stdin while alive: no line buffering, no echo, no
/// signal keys (`C-c` is read as a byte).
#[cfg(unix)]
struct Raw {
    saved: [u8; TERMIOS_SIZE],
}

/// Room for the platform's `struct termios` (72 bytes on macOS, 60 on
/// Linux).
#[cfg(unix)]
const TERMIOS_SIZE: usize = 256;

#[cfg(target_os = "macos")]
mod term {
    pub const FLAG_BYTES: usize = 8;
    pub const LFLAG_AT: usize = 24;
    pub const CC_AT: usize = 32;
    pub const ECHO: u64 = 0x8;
    pub const ICANON: u64 = 0x100;
    pub const ISIG: u64 = 0x80;
    pub const IEXTEN: u64 = 0x400;
    pub const VMIN: usize = 16;
    pub const VTIME: usize = 17;
}

#[cfg(all(unix, not(target_os = "macos")))]
mod term {
    pub const FLAG_BYTES: usize = 4;
    pub const LFLAG_AT: usize = 12;
    pub const CC_AT: usize = 17;
    pub const ECHO: u64 = 0o10;
    pub const ICANON: u64 = 0o2;
    pub const ISIG: u64 = 0o1;
    pub const IEXTEN: u64 = 0o100000;
    pub const VMIN: usize = 6;
    pub const VTIME: usize = 5;
}

#[cfg(unix)]
unsafe extern "C" {
    fn tcgetattr(fd: i32, termios: *mut u8) -> i32;
    fn tcsetattr(fd: i32, action: i32, termios: *const u8) -> i32;
}

/// `TCSANOW` (the same on macOS and Linux): keeps input typed ahead.
#[cfg(unix)]
const TCSANOW: i32 = 0;

#[cfg(unix)]
impl Raw {
    fn enter() -> Option<Self> {
        use std::io::IsTerminal;
        if !std::io::stdin().is_terminal() {
            return None;
        }
        let mut saved = [0u8; TERMIOS_SIZE];
        // SAFETY: the buffer is larger than any `struct termios`.
        if unsafe { tcgetattr(0, saved.as_mut_ptr()) } != 0 {
            return None;
        }
        let mut raw = saved;
        let at = term::LFLAG_AT..term::LFLAG_AT + term::FLAG_BYTES;
        let mut flag = [0u8; 8];
        flag[..term::FLAG_BYTES].copy_from_slice(&raw[at.clone()]);
        let lflag =
            u64::from_ne_bytes(flag) & !(term::ECHO | term::ICANON | term::ISIG | term::IEXTEN);
        raw[at].copy_from_slice(&lflag.to_ne_bytes()[..term::FLAG_BYTES]);
        raw[term::CC_AT + term::VMIN] = 1;
        raw[term::CC_AT + term::VTIME] = 0;
        // SAFETY: `raw` is a `struct termios` read by `tcgetattr`.
        (unsafe { tcsetattr(0, TCSANOW, raw.as_ptr()) } == 0).then_some(Self { saved })
    }
}

#[cfg(unix)]
impl Drop for Raw {
    fn drop(&mut self) {
        // SAFETY: `saved` is what `tcgetattr` filled in.
        unsafe {
            tcsetattr(0, TCSANOW, self.saved.as_ptr());
        }
    }
}

/// Windows: the console's input without line input, echo and Ctrl-C
/// processing, keys as VT sequences (`ESC [ A`, ..); its output
/// interpreting them.
#[cfg(windows)]
struct Raw {
    saved: [(Handle, u32); 2],
}

#[cfg(windows)]
type Handle = *mut std::ffi::c_void;

#[cfg(windows)]
unsafe extern "system" {
    fn GetStdHandle(which: u32) -> Handle;
    fn GetConsoleMode(h: Handle, mode: *mut u32) -> i32;
    fn SetConsoleMode(h: Handle, mode: u32) -> i32;
}

#[cfg(windows)]
impl Raw {
    fn enter() -> Option<Self> {
        const STD_INPUT: u32 = -10i32 as u32;
        const STD_OUTPUT: u32 = -11i32 as u32;
        const PROCESSED_INPUT: u32 = 0x1;
        const LINE_INPUT: u32 = 0x2;
        const ECHO_INPUT: u32 = 0x4;
        const VT_INPUT: u32 = 0x200;
        const VT_PROCESSING: u32 = 0x4;
        let mode = |which| {
            // SAFETY: a std handle and an out parameter.
            let h = unsafe { GetStdHandle(which) };
            let mut m = 0;
            (unsafe { GetConsoleMode(h, &mut m) } != 0).then_some((h, m))
        };
        let (input, output) = (mode(STD_INPUT)?, mode(STD_OUTPUT)?);
        let raw = Self {
            saved: [input, output],
        };
        let set = |(h, m)| {
            // SAFETY: a console handle `GetConsoleMode` accepted.
            unsafe { SetConsoleMode(h, m) != 0 }
        };
        let raw_in = (input.1 & !(PROCESSED_INPUT | LINE_INPUT | ECHO_INPUT)) | VT_INPUT;
        (set((input.0, raw_in)) && set((output.0, output.1 | VT_PROCESSING))).then_some(raw)
    }
}

#[cfg(windows)]
impl Drop for Raw {
    fn drop(&mut self) {
        for (h, m) in self.saved {
            // SAFETY: restores the mode `GetConsoleMode` read.
            unsafe { SetConsoleMode(h, m) };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn state(s: &str, pos: usize) -> State {
        State {
            buf: s.chars().collect(),
            pos,
            hist: 2,
            draft: Vec::new(),
        }
    }

    #[test]
    fn edits_and_history() {
        let mut st = state("let x = foo bar", 15);
        st.kill_word();
        assert_eq!(st.buf.iter().collect::<String>(), "let x = foo ");
        let history = ["a".to_owned(), "b".to_owned()];
        st.recall(&history, -1);
        assert_eq!(st.buf.iter().collect::<String>(), "b");
        st.recall(&history, -1);
        st.recall(&history, -1);
        assert_eq!(st.buf.iter().collect::<String>(), "a");
        st.recall(&history, 1);
        st.recall(&history, 1);
        assert_eq!(st.buf.iter().collect::<String>(), "let x = foo ");
        assert_eq!(utf8(0xc3, &mut &[0xa9u8][..]), Some('é'));
        assert_eq!(escape(&mut &b"[3~"[..]).as_deref(), Some("[3~"));
    }
}
