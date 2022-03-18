use crate::Piece;
use std::{
    error::Error,
    fmt::{Display, Formatter, Result as FmtResult},
    str::FromStr,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseSquareError {
    Malformed,
    BadColumn,
    BadRow,
}

impl Error for ParseSquareError {}

impl Display for ParseSquareError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use ParseSquareError::*;

        match self {
            Malformed => "malformed square",
            BadColumn => "found column not in range 'a'-'h'",
            BadRow => "found row not in range '1'-'8'",
        }
        .fmt(f)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Square {
    column: u8,
    row: u8,
}

impl FromStr for Square {
    type Err = ParseSquareError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.chars();
        if let Some(column_char) = chars.next() {
            if let Some(row_char) = chars.next() {
                if chars.next() == None {
                    let column = (column_char as u32).wrapping_sub('a' as u32);
                    let row = (row_char as u32).wrapping_sub('1' as u32);
                    return if column >= 8 {
                        Err(ParseSquareError::BadColumn)
                    } else if row >= 8 {
                        Err(ParseSquareError::BadRow)
                    } else {
                        Ok(Square {
                            row: row as u8,
                            column: column as u8,
                        })
                    };
                }
            }
        }

        Err(ParseSquareError::Malformed)
    }
}

impl Display for Square {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "{}{}",
            (b'a' + self.column) as char,
            (b'1' + self.row) as char
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseDirectionError {
    Malformed,
    Unknown,
}

impl Error for ParseDirectionError {}

impl Display for ParseDirectionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use ParseDirectionError::*;

        match self {
            Malformed => "a direction consists of exactly one character",
            Unknown => "character was not '+', '-', '>', '<'",
        }
        .fmt(f)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Direction {
    Up,
    Down,
    Right,
    Left,
}

impl FromStr for Direction {
    type Err = ParseDirectionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.chars();
        if let Some(c) = chars.next() {
            if chars.next() == None {
                return match c {
                    '+' => Ok(Self::Up),
                    '-' => Ok(Self::Down),
                    '>' => Ok(Self::Right),
                    '<' => Ok(Self::Left),
                    _ => Err(ParseDirectionError::Unknown),
                };
            }
        }

        Err(ParseDirectionError::Malformed)
    }
}

impl Display for Direction {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Up => '+',
            Self::Down => '-',
            Self::Right => '>',
            Self::Left => '<',
        }
        .fmt(f)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParsePatternError {
    Malformed,
    Ambiguous,
    TooLong,
    TooBig,
}

impl Error for ParsePatternError {}

impl Display for ParsePatternError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use ParsePatternError::*;

        match self {
            Malformed => "found unexpected characters in pattern",
            Ambiguous => "there is more than one valid interpretation of an empty pattern",
            TooLong => "pattern drops pieces on more squares than possible on largest supported board size (8)",
            TooBig => "pattern drops more pieces than highest supported carry limit (8)",
        }
        .fmt(f)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pattern(u8);

impl FromStr for Pattern {
    type Err = ParsePatternError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn shift(c: char) -> Result<u32, ParsePatternError> {
            let shift = (c as u32).wrapping_sub('1' as u32);
            if shift < 8 {
                Ok(shift)
            } else {
                Err(ParsePatternError::Malformed)
            }
        }

        let mut chars = s.chars();

        let segment_result = chars.by_ref().take(7).try_fold(0u8, |acc, c| {
            let shift = shift(c)?;
            if shift < acc.trailing_zeros() {
                Ok(((acc >> 1) | 0x80) >> shift)
            } else {
                Err(ParsePatternError::TooBig)
            }
        });

        match chars.try_fold(false, |_, c| shift(c).map(|_| true)) {
            Ok(false) => match segment_result {
                Ok(0) => Err(ParsePatternError::Ambiguous),
                r => r.map(Self),
            },
            Ok(true) => Err(ParsePatternError::TooLong),
            Err(e) => Err(e),
        }
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let mut value = self.0;
        let mut prev = value.trailing_zeros();
        loop {
            value = value & (value - 1);
            let trailing = value.trailing_zeros();
            ((b'0' + (trailing - prev) as u8) as char).fmt(f)?;
            if value == 0 {
                return Ok(());
            }
            prev = trailing;
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Move {
    Place(Square, Piece),
    Spread(Square, Direction, Pattern),
}
