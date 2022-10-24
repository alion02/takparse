use crate::Piece;
use std::{
    error::Error,
    fmt::{Display, Formatter, Result as FmtResult},
    str::FromStr,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Square {
    column: u8,
    row: u8,
}

impl Square {
    pub fn new(column: u8, row: u8) -> Self {
        assert!(column < 8);
        assert!(row < 8);
        Self { column, row }
    }

    pub fn shift(self, direction: Direction, amount: i8) -> Self {
        let Self { column, row } = self;
        let (x, y) = direction.offset();
        Self::new(
            x.checked_mul(amount)
                .unwrap()
                .checked_add(column as i8)
                .unwrap() as u8,
            y.checked_mul(amount)
                .unwrap()
                .checked_add(row as i8)
                .unwrap() as u8,
        )
    }

    pub fn column(self) -> u8 {
        self.column
    }

    pub fn row(self) -> u8 {
        self.row
    }

    const fn assert_on_board(self, board_size: u8) {
        assert!(self.row < board_size);
        assert!(self.column < board_size);
    }

    /// Generate a Square that is one step in the direction from this Square.
    /// If the generated Square is outside of the board, then this returns None instead.
    pub fn checked_step(self, direction: Direction, board_size: u8) -> Option<Self> {
        self.assert_on_board(board_size);
        use Direction::*;
        let (column, row) = (self.column, self.row);
        let (column, row) = match direction {
            Up => (column, row.checked_add(1).filter(|&y| y < board_size)?),
            Down => (column, row.checked_sub(1)?),
            Left => (column.checked_sub(1)?, row),
            Right => (column.checked_add(1).filter(|&x| x < board_size)?, row),
        };
        Some(Self { column, row })
    }

    /// Rotate 1 quarter turn clockwise.
    #[must_use]
    pub const fn rotate(self, board_size: u8) -> Self {
        self.assert_on_board(board_size);
        Self {
            column: self.row,
            row: board_size - 1 - self.column,
        }
    }

    /// Mirror along the horizontal axis.
    #[must_use]
    pub const fn mirror(self, board_size: u8) -> Self {
        self.assert_on_board(board_size);
        Self {
            column: self.column,
            row: board_size - 1 - self.row,
        }
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

impl FromStr for Square {
    type Err = ParseSquareError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use ParseSquareError::*;

        let mut chars = s.chars();
        if let Some(column_char) = chars.next() {
            if let Some(row_char) = chars.next() {
                if chars.next().is_none() {
                    let column = (column_char as u32).wrapping_sub('a' as u32);
                    let row = (row_char as u32).wrapping_sub('1' as u32);
                    return if column >= 8 {
                        Err(BadColumn)
                    } else if row >= 8 {
                        Err(BadRow)
                    } else {
                        Ok(Square {
                            row: row as u8,
                            column: column as u8,
                        })
                    };
                }
            }
        }

        Err(Malformed)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Direction {
    Up,
    Down,
    Right,
    Left,
}

impl Direction {
    pub fn offset(self) -> (i8, i8) {
        match self {
            Self::Up => (0, 1),
            Self::Down => (0, -1),
            Self::Right => (1, 0),
            Self::Left => (-1, 0),
        }
    }

    /// Rotate 1 quarter turn clockwise.
    #[must_use]
    pub const fn rotate(self) -> Self {
        use Direction::*;
        match self {
            Up => Right,
            Down => Left,
            Left => Up,
            Right => Down,
        }
    }

    /// Mirror along the horizontal axis. Up and Down get flipped.
    #[must_use]
    pub const fn mirror(self) -> Self {
        use Direction::*;
        match self {
            Up => Down,
            Down => Up,
            Left => Left,
            Right => Right,
        }
    }
}

impl From<Direction> for (i8, i8) {
    fn from(d: Direction) -> Self {
        d.offset()
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
pub enum ParseDirectionError {
    BadLength,
    BadChar,
}

impl Error for ParseDirectionError {}

impl Display for ParseDirectionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use ParseDirectionError::*;

        match self {
            BadLength => "direction did not consist of exactly 1 character",
            BadChar => "unknown direction character (not '+', '-', '>', '<')",
        }
        .fmt(f)
    }
}

impl FromStr for Direction {
    type Err = ParseDirectionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use ParseDirectionError::*;

        let mut chars = s.chars();
        if let Some(c) = chars.next() {
            if chars.next().is_none() {
                return Ok(match c {
                    '+' => Self::Up,
                    '-' => Self::Down,
                    '>' => Self::Right,
                    '<' => Self::Left,
                    _ => Err(BadChar)?,
                });
            }
        }

        Err(BadLength)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DropCounts(u32);

impl DropCounts {
    fn new(p: Pattern) -> Self {
        Self((p.0 as u32) << 24)
    }
}

impl Iterator for DropCounts {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0 != 0 {
            let prev = self.0.trailing_zeros();
            self.0 &= self.0 - 1;
            Some(self.0.trailing_zeros() - prev)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pattern(u8);

impl Pattern {
    pub fn from_mask(mask: u8) -> Self {
        assert!(mask != 0x00 && mask != 0xFF);
        Self(mask)
    }

    pub fn mask(self) -> u8 {
        self.0
    }

    pub fn drop_counts(self) -> DropCounts {
        DropCounts::new(self)
    }

    pub fn count_pieces(self) -> u32 {
        u8::BITS - self.0.trailing_zeros()
    }

    pub fn count_squares(self) -> u32 {
        self.0.count_ones()
    }

    pub fn count_final_square_pieces(self) -> u32 {
        self.0.leading_zeros() + 1
    }

    unsafe fn drop_all_unchecked(pieces: u32) -> Pattern {
        Self(1u8.rotate_right(pieces))
    }
}

impl FromIterator<u32> for Pattern {
    fn from_iter<T: IntoIterator<Item = u32>>(iter: T) -> Self {
        Self::from_mask(iter.into_iter().fold(0u8, |acc, count| {
            let shift = count - 1;
            assert!(shift < acc.trailing_zeros());
            ((acc >> 1) | 0x80) >> shift
        }))
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if self.count_squares() == 1 {
            Ok(())
        } else {
            self.drop_counts()
                .try_for_each(|count| ((b'0' + count as u8) as char).fmt(f))
        }
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
            Ambiguous => "found ambiguous empty pattern (its interpretation is dependent on taken piece count)",
            TooLong => "pattern drops pieces on more squares than possible on largest supported board size (8)",
            TooBig => "pattern drops more pieces than highest supported carry limit (8)",
        }
        .fmt(f)
    }
}

impl FromStr for Pattern {
    type Err = ParsePatternError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use ParsePatternError::{self as E, *};

        fn shift(c: char) -> Result<u32, E> {
            let shift = (c as u32).wrapping_sub('1' as u32);
            if shift < 8 {
                Ok(shift)
            } else {
                Err(Malformed)
            }
        }

        let mut chars = s.chars();

        let segment = chars.by_ref().take(7).try_fold(0u8, |acc, c| {
            let shift = shift(c)?;
            if shift < acc.trailing_zeros() {
                Ok(((acc >> 1) | 0x80) >> shift)
            } else {
                Err(TooBig)
            }
        })?;

        match chars.try_fold(false, |_, c| shift(c).map(|_| true)) {
            Ok(false) => match segment {
                0 => Err(Ambiguous),
                s => Ok(Self(s)),
            },
            Ok(true) => Err(TooLong),
            Err(e) => Err(e),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MoveKind {
    Place(Piece),
    Spread(Direction, Pattern),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Move {
    square: Square,
    kind: MoveKind,
}

impl Move {
    pub fn new(square: Square, kind: MoveKind) -> Self {
        Self { square, kind }
    }

    pub fn square(self) -> Square {
        self.square
    }

    pub fn kind(self) -> MoveKind {
        self.kind
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseMoveError {
    Square(ParseSquareError),
    Direction(ParseDirectionError),
    Pattern(ParsePatternError),
    Malformed,
    BadPieceOrCount,
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
                BadPieceOrCount => "move prefix was not a valid piece or count",
                TruncatedSpread => "spread is missing both a direction and a pattern",
                BadPlacement => "placement has trailing characters",
                CountMismatch => "number of pieces taken does not match number of dropped",
                BadCrush => "declared crush but dropping more than one piece on final square",
                Square(_) | Direction(_) | Pattern(_) => unreachable!(),
            }
            .fmt(f)
        }
    }
}

impl FromStr for Move {
    type Err = ParseMoveError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use self::Pattern as PatternType;
        use ParseMoveError::*;

        let s = s.trim_end_matches(['?', '!', '\'', '"']);
        if s.len() < 2 || !s.is_ascii() {
            return Err(Malformed);
        }

        let mut piece = None;
        let mut taken_count = None;
        let mut rest = &s[2..];
        let square = s[..2].parse().or_else(|e| {
            Ok(if s.len() < 3 {
                Err(e)
            } else {
                if let Ok(p) = s[..1].parse() {
                    piece = Some(p);
                } else {
                    let byte = s.as_bytes()[0];
                    let c = byte.wrapping_sub(b'1');
                    if c < 8 {
                        taken_count = Some(c + 1);
                    } else {
                        return Err(BadPieceOrCount);
                    }
                }
                rest = &s[3..];
                s[1..3].parse()
            }?)
        })?;

        Ok(Self {
            square,
            kind: if rest.is_empty() {
                if taken_count.is_some() {
                    Err(TruncatedSpread)?
                } else {
                    MoveKind::Place(piece.unwrap_or_default())
                }
            } else if piece.is_some() {
                Err(BadPlacement)?
            } else {
                let direction = rest[..1].parse()?;

                let crush = rest.strip_suffix('*').map(|r| rest = r).is_some();

                let taken_count = taken_count.unwrap_or(1) as u32;
                let pattern = rest[1..].parse().or_else(|e| match e {
                    ParsePatternError::Ambiguous => {
                        Ok(unsafe { PatternType::drop_all_unchecked(taken_count) })
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
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::*;

    #[test]
    fn common_moves() {
        round_trip::<Move, _, _>([
            "a1",
            "h8",
            "Sa3",
            "Cb4",
            "c2<",
            "3c5+",
            "4h4-13",
            "7a5>3112",
            "8h1<1112111",
        ])
    }

    #[test]
    fn uncanonical_moves() {
        transform::<Move, _, _>([
            ("Fa1", "a1"),
            ("c1>1", "c1>"),
            ("1b1>1", "b1>"),
            ("4a4-4", "4a4-"),
            ("f7-*", "f7-"),
            ("5d2>131*", "5d2>131"),
            ("a5??", "a5"),
            ("b8\"!", "b8"),
            ("8g3<112121*'!?", "8g3<112121"),
        ])
    }

    #[test]
    fn invalid_moves() {
        use ParseMoveError::*;

        error::<Move, _, _>(["ąąąą", "ą", "", "a", "5", "S"], Malformed);
        error::<Move, _, _>(
            ["i1", "H8", "11", "Su5"],
            Square(ParseSquareError::BadColumn),
        );
        error::<Move, _, _>(["af", "a9", "a0", "6cA<"], Square(ParseSquareError::BadRow));
        error::<Move, _, _>(["9a1>", "ca4"], BadPieceOrCount);
        error::<Move, _, _>(["5b6", "1g1"], TruncatedSpread);
        error::<Move, _, _>(["Fe8<", "Cd4*"], BadPlacement);
        error::<Move, _, _>(["3f3}", "h1/"], Direction(ParseDirectionError::BadChar));
        error::<Move, _, _>(
            ["6b2>21012", "3a7-."],
            Pattern(ParsePatternError::Malformed),
        );
        error::<Move, _, _>(
            ["4d2+324", "7f5<81111111111111"],
            Pattern(ParsePatternError::TooBig),
        );
        error::<Move, _, _>(["8a3>11111111"], Pattern(ParsePatternError::TooLong));
        error::<Move, _, _>(["2c1+111"], CountMismatch);
        error::<Move, _, _>(["3d5<*"], BadCrush);
    }

    #[test]
    fn checked_step() {
        let s = Square::new;
        assert_eq!(s(2, 1).checked_step(Direction::Up, 3), Some(s(2, 2)));
        assert_eq!(s(2, 3).checked_step(Direction::Up, 4), None);
        assert_eq!(s(4, 5).checked_step(Direction::Down, 6), Some(s(4, 4)));
        assert_eq!(s(4, 0).checked_step(Direction::Down, 6), None);
        assert_eq!(s(2, 1).checked_step(Direction::Left, 3), Some(s(1, 1)));
        assert_eq!(s(0, 1).checked_step(Direction::Left, 3), None);
        assert_eq!(s(0, 0).checked_step(Direction::Right, 2), Some(s(1, 0)));
        assert_eq!(s(0, 0).checked_step(Direction::Right, 1), None);
    }

    #[test]
    fn rotate_even() {
        let s = Square::new;
        // corner
        let sq = s(0, 0);
        assert_eq!(sq.rotate(6), s(0, 5));
        assert_eq!(sq.rotate(6).rotate(6), s(5, 5));
        assert_eq!(sq.rotate(6).rotate(6).rotate(6), s(5, 0));
        assert_eq!(sq.rotate(6).rotate(6).rotate(6).rotate(6), s(0, 0));
        // centre
        let sq = s(2, 2);
        assert_eq!(sq.rotate(6), s(2, 3));
        assert_eq!(sq.rotate(6).rotate(6), s(3, 3));
        assert_eq!(sq.rotate(6).rotate(6).rotate(6), s(3, 2));
        assert_eq!(sq.rotate(6).rotate(6).rotate(6).rotate(6), s(2, 2));
    }

    #[test]
    fn rotate_odd() {
        let s = Square::new;
        // corner
        let sq = s(0, 0);
        assert_eq!(sq.rotate(7), s(0, 6));
        assert_eq!(sq.rotate(7).rotate(7), s(6, 6));
        assert_eq!(sq.rotate(7).rotate(7).rotate(7), s(6, 0));
        assert_eq!(sq.rotate(7).rotate(7).rotate(7).rotate(7), s(0, 0));
        // centre
        let sq = s(3, 3);
        assert_eq!(sq.rotate(7), s(3, 3));
    }

    #[test]
    fn mirror_even() {
        let square = Square::new(1, 2);
        assert_eq!(square.mirror(6), Square::new(1, 3));
        assert_eq!(square.mirror(6).mirror(6), Square::new(1, 2));
    }

    #[test]
    fn mirror_odd() {
        let square = Square::new(4, 1);
        assert_eq!(square.mirror(7), Square::new(4, 5));
        assert_eq!(square.mirror(7).mirror(7), Square::new(4, 1));

        // centre line
        let square = Square::new(2, 3);
        assert_eq!(square.mirror(7), Square::new(2, 3));
    }
}
