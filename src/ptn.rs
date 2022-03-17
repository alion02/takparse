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
pub struct Pattern(u8);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Move {
    Place(Square, Piece),
    Spread(Square, Direction, Pattern),
}
