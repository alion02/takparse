use crate::Piece;
use std::{
    error::Error,
    fmt::{Display, Formatter, Result as FmtResult},
    str::FromStr,
};

/// A location on the board.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Square {
    column: u8,
    row: u8,
}

impl Square {
    /// Creates a new [`Square`].
    ///
    /// Both arguments are zero-indexed.
    /// The constructor asserts that both the column and row are smaller than 8.
    ///
    /// # Panics
    ///
    /// Panics if either of the arguments is greater or equal to 8.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::Square;
    /// assert_eq!(Square::new(0, 0).to_string(), "a1");
    /// assert_eq!(Square::new(1, 0).to_string(), "b1");
    /// assert_eq!(Square::new(0, 1).to_string(), "a2");
    /// ```
    ///
    /// ```should_panic
    /// # use takparse::Square;
    /// assert_eq!(Square::new(25, 8).to_string(), "z9"); // fails
    /// ```
    pub fn new(column: u8, row: u8) -> Self {
        assert!(column < 8);
        assert!(row < 8);
        Self { column, row }
    }

    /// Shifts a square by `amount` in `direction`.
    ///
    /// This is used when we want to find a relative square, such as when calculating a spread.
    ///
    /// # Panics
    ///
    /// Panics when the shift would create an invalid square.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Direction, Square, ParseSquareError};
    /// let square: Square = "c3".parse()?;
    /// assert_eq!(square.shift(Direction::Up, 1).to_string(), "c4");
    /// assert_eq!(square.shift(Direction::Left, 2).to_string(), "a3");
    /// # Ok::<(), ParseSquareError>(())
    /// ```
    ///
    /// ```should_panic
    /// # use takparse::{Direction, Square, ParseSquareError};
    /// let square: Square = "c3".parse()?;
    /// assert_eq!(square.shift(Direction::Down, 3).to_string(), "c0"); // fails
    /// # Ok::<(), ParseSquareError>(())
    /// ```
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

    /// Getter for `column`.
    pub fn column(self) -> u8 {
        self.column
    }

    /// Getter for `row`.
    pub fn row(self) -> u8 {
        self.row
    }

    const fn assert_on_board(self, board_size: u8) {
        assert!(self.row < board_size);
        assert!(self.column < board_size);
    }

    /// Generate a square that is one step in the direction from this square.
    /// If the generated square is outside of the board, then this returns [`None`] instead.
    ///
    /// # Panics
    ///
    /// Panics if the square is not on the board with the given `board_size`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Direction, Square, ParseSquareError};
    /// let square: Square = "e3".parse()?;
    /// assert_eq!(
    ///     square.checked_step(Direction::Up, 5),
    ///     Some("e4".parse()?)
    /// );
    /// assert_eq!(square.checked_step(Direction::Right, 5), None);
    /// # Ok::<(), ParseSquareError>(())
    /// ```
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

    /// Rotate the square 1 quarter turn clockwise around the center of the board.
    ///
    /// # Panics
    ///
    /// Panics if the square is not on the board with the given `board_size`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Square, ParseSquareError};
    /// let square: Square = "b2".parse()?;
    /// assert_eq!(square.rotate(6).to_string(), "b5");
    /// assert_eq!(square.rotate(6).rotate(6).to_string(), "e5");
    /// assert_eq!(square.rotate(6).rotate(6).rotate(6).to_string(), "e2");
    /// assert_eq!(square.rotate(6).rotate(6).rotate(6).rotate(6), square);
    /// # Ok::<(), ParseSquareError>(())
    /// ```
    #[must_use]
    pub const fn rotate(self, board_size: u8) -> Self {
        self.assert_on_board(board_size);
        Self {
            column: self.row,
            row: board_size - 1 - self.column,
        }
    }

    /// Mirror the square along the horizontal axis going through the center of the board.
    ///
    /// # Panics
    ///
    /// Panics if the square is not on the board with the given `board_size`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Square, ParseSquareError};
    /// let square: Square = "b2".parse()?;
    /// assert_eq!(square.mirror(6).to_string(), "b5");
    /// assert_eq!(square.mirror(5).to_string(), "b4");
    /// # Ok::<(), ParseSquareError>(())
    /// ```
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

/// Error returned when something goes wrong during the parsing of a [`Square`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseSquareError {
    /// Returned when the string is the wrong length. Squares should be exactly two characters.
    Malformed,
    /// Returned when the column character is not valid.
    /// This could mean it is not a letter, or that the letter is out of range for squares.
    BadColumn,
    /// Returned when the row character is not valid.
    /// This could mean that it is not a number, or that the number is out of range for squares.
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
                if chars.next() == None {
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

/// Enum representing a direction to move on the board.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Direction {
    /// Positive vertical direction, represented with '+'.
    Up,
    /// Negative vertical direction, represented with '-'.
    Down,
    /// Positive horizontal direction, represented with '>'.
    Right,
    /// Negative horizontal direction, represented with '<'.
    Left,
}

impl Direction {
    /// Gets the offset for a given direction.
    /// The offset is a pair of numbers,
    /// where the first represents the change in the column,
    /// and the second number represents the change in the row.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::Direction;
    /// assert_eq!(Direction::Up.offset(), (0, 1));
    /// assert_eq!(Direction::Left.offset(), (-1, 0));
    /// ```
    pub fn offset(self) -> (i8, i8) {
        match self {
            Self::Up => (0, 1),
            Self::Down => (0, -1),
            Self::Right => (1, 0),
            Self::Left => (-1, 0),
        }
    }

    /// Rotate the direction 1 quarter turn clockwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::Direction;
    /// assert_eq!(Direction::Up.rotate(), Direction::Right);
    /// assert_eq!(Direction::Left.rotate(), Direction::Up);
    /// ```
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

    /// Mirror the direction along the horizontal axis. Up and Down get flipped.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::Direction;
    /// assert_eq!(Direction::Up.mirror(), Direction::Down);
    /// assert_eq!(Direction::Left.mirror(), Direction::Left);
    /// ```
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

/// Error returned when something goes wrong during the parsing of a [`Direction`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseDirectionError {
    /// Directions should be exactly one character in length. This variant is returned if they are not.
    BadLength,
    /// Directions can only be one '+', '-', '>', and '<'. Anything else returns this variant.
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
            if chars.next() == None {
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

/// A helper struct for iterating over the drop counts encoded in a [`Pattern`].
///
/// Drop counts are the numbers which say how many stones to drop on a square before moving on.
///
/// # Examples
///
/// ```
/// # use takparse::{Move, MoveKind, ParseMoveError};
/// let spread: Move = "6a1+123".parse()?;
/// if let MoveKind::Spread(_direction, pattern) = spread.kind() {
///     let counts: Vec<u32> = pattern.drop_counts().into_iter().collect();
///     assert_eq!(counts, vec![1, 2, 3]);
/// }
/// # Ok::<(), ParseMoveError>(())
/// ```
///
/// ```
/// # use takparse::Pattern;
/// let pattern = Pattern::from_mask(0b0010_1100);
/// // for loops can omit `.into_iter()`
/// for count in pattern.drop_counts() {
///     // prints 1 2 3
///     println!("{count}");
/// }
/// ```
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

/// An encoded version of the drop counts.
///
/// The drop counts represent how many pieces to drop
/// on each square as a stack is spread across the board.
///
/// You are most likely not going to need to interact with this encoding directly.
/// A much more common use case is to use the drop counts as [`DropCounts`]
/// which you can get from [`Pattern::drop_counts`].
///
/// # Encoding
///
/// The encoding, when read from least significant bit to most significant bit,
/// is as follows:
/// - Pick up 8 and begin on the current square.
/// - Every time we encounter a zero, drop a piece on the current square.
/// - Every time we encounter a one, move to the next square and drop a piece.
///
/// For example, the pattern for the move `6a1>123` becomes `0010 1100`.
/// Here is how that encoding can be read (least significant to most significant):
///
/// - First we pick up 8.
/// - Drop two, once for each of the zeroes on the right. `00` (Essentially we pick up 6)
/// - Move a step and drop one. `1`
/// - Move a step and drop two. `01`
/// - Finally we move a step and drop three. `001`
///
/// # Examples
///
/// ```
/// # use takparse::{Move, MoveKind, ParseMoveError};
/// let spread: Move = "6a1+123".parse()?;
/// if let MoveKind::Spread(_direction, pattern) = spread.kind() {
///     assert_eq!(pattern.mask(), 0b0010_1100);
/// }
/// # Ok::<(), ParseMoveError>(())
/// ```
///
/// ```
/// # use takparse::{Move, MoveKind, ParseMoveError};
/// let spread: Move = "4a1+121".parse()?;
/// if let MoveKind::Spread(_direction, pattern) = spread.kind() {
///     assert_eq!(pattern.mask(), 0b1011_0000);
/// }
/// # Ok::<(), ParseMoveError>(())
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pattern(u8);

impl Pattern {
    /// Create a [`Pattern`] from a mask.
    ///
    /// # Panics
    ///
    /// Panics if the mask is all zeroes or all ones.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Move, MoveKind, Pattern, ParseMoveError};
    /// let spread: Move = "3a1>21".parse()?;
    /// if let MoveKind::Spread(_direction, pattern) = spread.kind() {
    ///     assert_eq!(Pattern::from_mask(0b1010_0000), pattern);
    /// }
    /// # Ok::<(), ParseMoveError>(())
    /// ```
    pub fn from_mask(mask: u8) -> Self {
        assert!(mask != 0x00 && mask != 0xFF);
        Self(mask)
    }

    /// Getter for `mask`.
    pub fn mask(self) -> u8 {
        self.0
    }

    /// Consumes the `Pattern` and returns the corresponding `DropCounts`.
    ///
    /// This is the go-to way for iterating over drop counts.
    ///
    /// # Examples
    /// ```
    /// # use takparse::Pattern;
    /// let pattern = Pattern::from_mask(0b0111_0000);
    /// for count in pattern.drop_counts() {
    ///     // prints 1, 1, 2
    ///     println!("{count}");
    /// }
    pub fn drop_counts(self) -> DropCounts {
        DropCounts::new(self)
    }

    /// Calculates how many pieces are picked up.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Move, MoveKind, ParseMoveError};
    /// let spread: Move = "3a1>21".parse()?;
    /// if let MoveKind::Spread(_direction, pattern) = spread.kind() {
    ///     assert_eq!(pattern.count_pieces(), 3);
    /// }
    /// # Ok::<(), ParseMoveError>(())
    /// ```
    pub fn count_pieces(self) -> u32 {
        u8::BITS - self.0.trailing_zeros()
    }

    /// Counts how many squares this pattern covers.
    /// This does not include the origin square.
    /// A valid pattern always covers at least one square.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Move, MoveKind, ParseMoveError};
    /// let spread: Move = "3a1>21".parse()?;
    /// if let MoveKind::Spread(_direction, pattern) = spread.kind() {
    ///     assert_eq!(pattern.count_squares(), 2);
    /// }
    /// # Ok::<(), ParseMoveError>(())
    /// ```
    pub fn count_squares(self) -> u32 {
        self.0.count_ones()
    }

    /// Counts how many pieces are dropped on the final square.
    /// This can be used to check whether a smash only drops one piece for the final square.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Move, MoveKind, ParseMoveError};
    /// let spread: Move = "3a1>21".parse()?;
    /// if let MoveKind::Spread(_direction, pattern) = spread.kind() {
    ///     assert_eq!(pattern.count_final_square_pieces(), 1);
    /// }
    /// # Ok::<(), ParseMoveError>(())
    /// ```
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

/// Error returned when something goes wrong during the parsing of a [`Pattern`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParsePatternError {
    /// This variant is returned when there are invalid characters in the pattern.
    Malformed,
    /// This variant is returned when the pattern is equal to zero, which is an ambigious pattern.
    Ambiguous,
    /// The amount of drops should be less or equal to 8.
    TooLong,
    /// The sum of dropped pieces should less or equal to 8. If it is not, then this variant is returned.
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

/// Container enum for the two types of possible moves in Tak.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MoveKind {
    /// A place move specifies which type of piece was placed.
    Place(Piece),
    /// A spread includes a direction and the pattern of dropped pieces.
    Spread(Direction, Pattern),
}

/// Struct which represents a valid move in Tak.
///
/// A move can either be a placement or a spread.
/// In either case you need to specify a square.
/// When placing, `square` is the location of the placed piece.
/// When spreading, `square` is the origin of the spread -
/// it is the location of the stack which is picked up.
///
/// Which kind of move this represents is stored in the `kind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Move {
    square: Square,
    kind: MoveKind,
}

impl Move {
    /// Creates a new [`Move`] from the `square` and `kind`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Move, MoveKind, Square, Pattern, Direction, ParseMoveError};
    /// // Constructing the move from parts.
    /// let square: Square = "c2".parse()?;
    /// let pattern: Pattern = "123".parse()?;
    /// let kind: MoveKind = MoveKind::Spread(Direction::Up, pattern);
    /// let my_move = Move::new(square, kind);
    ///
    /// // Parsing a move.
    /// let parsed_move: Move = "6c2+123".parse()?;
    ///
    /// // We get the same thing at the end.
    /// assert_eq!(my_move, parsed_move);
    /// # Ok::<(), ParseMoveError>(())
    /// ```
    pub fn new(square: Square, kind: MoveKind) -> Self {
        Self { square, kind }
    }

    /// Getter for `square`.
    pub fn square(self) -> Square {
        self.square
    }

    /// Getter for `kind`.
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

/// Error returned when something goes wrong during the parsing of a [`Move`].
///
/// This enum encapsulates multiple other parse errors.
/// These variants are returned when that section of the parsing goes wrong.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseMoveError {
    /// Variant for when there was an error with the square.
    Square(ParseSquareError),
    /// Variant for when there was an issue with the direction.
    Direction(ParseDirectionError),
    /// Variant for when there was an problem with the pattern.
    Pattern(ParsePatternError),
    /// Returned when the move is too short or non-ascii.
    Malformed,
    /// Returned when the part before the square is wrong.
    /// For example is the piece prefix is incorrect, or the pick-up count is not valid.
    BadPieceOrCount,
    /// Returned when a spread is missing both a direction and drop count pattern.
    TruncatedSpread,
    /// Returned when a placement has invalid character after it.
    BadPlacement,
    /// Returned when the number of pieces picked up does not equal the number of pieces dropped in a spread.
    CountMismatch,
    /// When a crush is specified with '*' but the amount of dropped pieces
    /// on the last square is more than one, this variant is returned.
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
                if taken_count != None {
                    Err(TruncatedSpread)?
                } else {
                    MoveKind::Place(piece.unwrap_or_default())
                }
            } else {
                if piece != None {
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
