use crate::{Move, ParseMoveError};
use std::{
    error::Error,
    fmt::{Display, Formatter, Result as FmtResult},
    iter::once,
    str::FromStr,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Tag {
    key: String,
    value: String,
}

impl Tag {
    pub fn new<A: Into<String>, B: Into<String>>(key: A, value: B) -> Self {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    pub fn key(&self) -> &'_ str {
        &self.key
    }

    pub fn value(&self) -> &'_ str {
        &self.value
    }
}

impl Display for Tag {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "[{} \"{}\"]", self.key, self.value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseTagError {
    NoOpeningBracket,
    MissingKey,
    NoOpeningQuotationMarks,
    IllegalEscape,
    MissingValue,
    NoClosingQuotationMarks,
    NoClosingBracket,
    GarbageAfterValue,
    GarbageAfterTag,
}

impl Error for ParseTagError {}

impl Display for ParseTagError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::NoOpeningBracket => "missing opening square bracket '[' at the start",
            Self::MissingKey => "missing key",
            Self::NoOpeningQuotationMarks => "missing opening quotation marks '\"' before value",
            Self::IllegalEscape => "invalid character found after a backslash-escape in the value",
            Self::MissingValue => "missing value",
            Self::NoClosingQuotationMarks => "missing closing quotation marks '\"' after value",
            Self::GarbageAfterValue => "non-whitespace text after closing quotation mark '\"'",
            Self::NoClosingBracket => "missing closing square bracket ']' at the end",
            Self::GarbageAfterTag => "text after the closing square bracket ']'",
        }
        .fmt(f)
    }
}

impl FromStr for Tag {
    type Err = ParseTagError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.chars();

        // open bracket
        let Some('[') = chars.next() else {Err(ParseTagError::NoOpeningBracket)?};

        // key
        let mut opened = false;
        let mut key = String::new();
        for c in chars.by_ref() {
            if c == '"' {
                opened = true;
                break;
            }
            key.push(c);
        }
        if !opened {
            Err(ParseTagError::NoOpeningQuotationMarks)?;
        }
        let key = key.trim();
        if key.is_empty() {
            Err(ParseTagError::MissingKey)?;
        }

        // value
        let mut value = String::new();
        let mut escape = false;
        let mut closed = false;
        for c in chars.by_ref() {
            if escape {
                match c {
                    '"' | '\\' => escape = false,
                    _ => Err(ParseTagError::IllegalEscape)?,
                }
            } else if c == '\\' {
                escape = true;
                continue;
            } else if c == '"' {
                closed = true;
                break;
            }

            value.push(c);
        }
        if !closed {
            Err(ParseTagError::NoClosingQuotationMarks)?;
        }
        if value.is_empty() {
            Err(ParseTagError::MissingValue)?;
        }

        // closing bracket
        let mut closed = false;
        for c in chars.by_ref() {
            if c == ']' {
                closed = true;
                break;
            }
            if !c.is_whitespace() {
                Err(ParseTagError::GarbageAfterValue)?;
            }
        }
        if !closed {
            Err(ParseTagError::NoClosingBracket)?;
        }
        if chars.count() != 0 {
            Err(ParseTagError::GarbageAfterTag)?
        }

        Ok(Self::new(key, value))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum WinReason {
    Road,
    Flat,
    #[default]
    Other,
}

impl Display for WinReason {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Road => "R",
            Self::Flat => "F",
            Self::Other => "1",
        }
        .fmt(f)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum GameResult {
    White(WinReason),
    Black(WinReason),
    #[default]
    Draw,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseGameResultError {
    Invalid,
}

impl Display for ParseGameResultError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "invalid or unknown game result")
    }
}

impl Error for ParseGameResultError {}

impl Display for GameResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::White(reason) => write!(f, "{reason}-0"),
            Self::Black(reason) => write!(f, "0-{reason}"),
            Self::Draw => write!(f, "1/2-1/2"),
        }
    }
}

impl FromStr for GameResult {
    type Err = ParseGameResultError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "F-0" => GameResult::White(WinReason::Flat),
            "R-0" => GameResult::White(WinReason::Road),
            "1-0" => GameResult::White(WinReason::Other),
            "0-F" => GameResult::Black(WinReason::Flat),
            "0-R" => GameResult::Black(WinReason::Road),
            "0-1" => GameResult::Black(WinReason::Other),
            "1/2-1/2" => GameResult::Draw,
            _ => Err(ParseGameResultError::Invalid)?,
        })
    }
}

