mod ptn;
mod tps;

pub use ptn::*;
pub use tps::*;

use std::{
    error::Error,
    fmt::{Display, Formatter, Result as FmtResult},
    str::FromStr,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Piece {
    Flat,
    Wall,
    Cap,
}

impl Default for Piece {
    fn default() -> Self {
        Self::Flat
    }
}

impl Display for Piece {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Flat => "",
            Self::Wall => "S",
            Self::Cap => "C",
        }
        .fmt(f)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParsePieceError {
    TooLong,
    BadChar,
}

impl Error for ParsePieceError {}

impl Display for ParsePieceError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use ParsePieceError::*;

        match self {
            TooLong => "piece consisted of multiple characters",
            BadChar => "unknown piece character (not 'F', 'S', 'C')",
        }
        .fmt(f)
    }
}

impl FromStr for Piece {
    type Err = ParsePieceError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use ParsePieceError::*;

        let mut chars = s.chars();

        let c = chars.next();

        if chars.next() != None {
            Err(TooLong)?
        }

        Ok(match c.unwrap_or('F') {
            'F' => Self::Flat,
            'S' => Self::Wall,
            'C' => Self::Cap,
            _ => Err(BadChar)?,
        })
    }
}
