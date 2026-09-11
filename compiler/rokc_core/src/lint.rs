//! Lint levels, as `rok.rokon` `lints`, `-A/-W/-D` and `#[allow/warn/deny]` spell them.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Level {
    Allow,
    Warn,
    Deny,
}

impl Level {
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "allow" => Some(Self::Allow),
            "warn" => Some(Self::Warn),
            "deny" => Some(Self::Deny),
            _ => None,
        }
    }

    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Allow => "allow",
            Self::Warn => "warn",
            Self::Deny => "deny",
        }
    }

    /// The command-line flag setting this level.
    #[must_use]
    pub const fn flag(self) -> &'static str {
        match self {
            Self::Allow => "-A",
            Self::Warn => "-W",
            Self::Deny => "-D",
        }
    }

    #[must_use]
    pub fn from_flag(flag: &str) -> Option<Self> {
        match flag {
            "-A" | "--allow" => Some(Self::Allow),
            "-W" | "--warn" => Some(Self::Warn),
            "-D" | "--deny" => Some(Self::Deny),
            _ => None,
        }
    }
}
