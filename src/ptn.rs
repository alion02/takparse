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

impl Pattern {
    pub fn count_pieces(self) -> u32 {
        u8::BITS - self.0.trailing_zeros()
    }

    pub fn count_squares(self) -> u32 {
        self.0.count_ones()
    }

    pub fn count_final_square_pieces(self) -> u32 {
        self.0.leading_zeros() + 1
    }

    pub unsafe fn spread_to_one_unchecked(pieces: u32) -> Pattern {
        Self(1u8.rotate_right(pieces))
    }
}

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
        if self.count_squares() == 1 {
            return Ok(());
        }
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
pub enum ParseMoveError {
    Square(ParseSquareError),
    Direction(ParseDirectionError),
    Pattern(ParsePatternError),
    Malformed,
    BadSquarePieceOrCount,
    TruncatedSpread,
    BadPlacement,
    CountMismatch,
    BadCrush,
}

impl From<ParseSquareError> for ParseMoveError {
    fn from(value: ParseSquareError) -> Self {
        Self::Square(value)
    }
}

impl From<ParseDirectionError> for ParseMoveError {
    fn from(value: ParseDirectionError) -> Self {
        Self::Direction(value)
    }
}

impl From<ParsePatternError> for ParseMoveError {
    fn from(value: ParsePatternError) -> Self {
        Self::Pattern(value)
    }
}

impl Error for ParseMoveError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        use ParseMoveError::*;

        Some(match self {
            Square(e) => e,
            Direction(e) => e,
            Pattern(e) => e,
            _ => return None,
        })
    }
}

impl Display for ParseMoveError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use ParseMoveError::*;

        if let Some(e) = self.source() {
            Display::fmt(&e, f)
        } else {
            match self {
                Malformed => "not a valid ptn move",
                BadSquarePieceOrCount => "move does not begin with square, piece or count",
                TruncatedSpread => "spread is missing both a direction and a pattern",
                BadPlacement => "placement has trailing characters",
                CountMismatch => "number of pieces taken does not match number of deposited",
                BadCrush => "declared crush but leaving more than one piece on final square",
                Square(_) | Direction(_) | Pattern(_) => unreachable!(),
            }
            .fmt(f)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum MoveKind {
    Place(Piece),
    Spread(Direction, Pattern),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Move {
    square: Square,
    kind: MoveKind,
}

impl FromStr for Move {
    type Err = ParseMoveError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use crate::ptn::Pattern as PatternStruct;
        use ParseMoveError::*;

        let s = s.trim_end_matches(['?', '!', '\'', '"']);
        if s.len() < 2 || !s.is_ascii() {
            return Err(Malformed);
        }

        let mut piece = None;
        let mut taken_count = None;
        let mut rest = &s[2..];
        let square = s[..2].parse().or_else(|_| {
            if let Ok(p) = s[..1].parse() {
                piece = Some(p);
            } else {
                let byte = s.as_bytes()[0];
                let c = byte.wrapping_sub(b'1');
                if c < 8 {
                    taken_count = Some(c + 1);
                } else {
                    return Err(BadSquarePieceOrCount);
                }
            }

            if s.len() >= 3 {
                rest = &s[3..];
                &s[1..3]
            } else {
                &s[1..]
            }
            .parse()
            .map_err(Square)
        })?;

        Ok(Self {
            square,
            kind: if rest.len() == 0 {
                if taken_count != None {
                    Err(TruncatedSpread)?
                } else {
                    MoveKind::Place(piece.unwrap_or(Piece::Flat))
                }
            } else {
                if piece != None {
                    Err(BadPlacement)?
                } else {
                    let direction = rest[..1].parse()?;

                    let crush = if s.ends_with('*') {
                        rest = &rest[..rest.len() - 1];
                        true
                    } else {
                        false
                    };

                    let taken_count = taken_count.unwrap_or(1) as u32;
                    let pattern = rest[1..].parse().or_else(|e| match e {
                        ParsePatternError::Ambiguous => {
                            Ok(unsafe { PatternStruct::spread_to_one_unchecked(taken_count) })
                        }
                        _ => Err(e),
                    })?;

                    if pattern.count_pieces() != taken_count {
                        Err(CountMismatch)?
                    } else if crush && pattern.count_final_square_pieces() != 1 {
                        Err(BadCrush)?
                    } else {
                        MoveKind::Spread(direction, pattern)
                    }
                }
            },
        })
    }
}

impl Display for Move {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let Self { square, kind } = self;
        match kind {
            MoveKind::Place(piece) => write!(f, "{piece}{square}"),
            MoveKind::Spread(direction, pattern) => {
                let count = pattern.count_pieces();
                if count != 1 {
                    count.fmt(f)?;
                }
                write!(f, "{square}{direction}{pattern}")
            }
        }
    }
}
