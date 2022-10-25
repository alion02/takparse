use crate::Piece;
use std::{
    error::Error,
    fmt::{Display, Formatter, Result as FmtResult},
    iter::{once, repeat},
    num::{IntErrorKind, NonZeroUsize},
    ops::Not,
    str::FromStr,
};

// TODO: granular error types

/// Enum for the player and piece color.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Color {
    /// Player who makes the first move.
    White,
    /// Player who goes second.
    Black,
}

impl FromStr for Color {
    type Err = ParseTpsError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "1" => Ok(Self::White),
            "2" => Ok(Self::Black),
            "" => Err(ParseTpsError::MissingColor),
            _ => Err(ParseTpsError::InvalidColor),
        }
    }
}

impl Display for Color {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::White => '1',
            Self::Black => '2',
        }
        .fmt(f)
    }
}

impl Not for Color {
    type Output = Self;
    fn not(self) -> Self::Output {
        match self {
            Self::White => Self::Black,
            Self::Black => Self::White,
        }
    }
}

/// A stack is one or more pieces on top of each other.
/// Yes, even a single flat on its own is considered a stack.
///
/// Since only flat pieces can be stacked on, we only need to know the top [`Piece`].
/// The rest of the stack is encoded as colors of the flats from the bottom of the stack to the top.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Stack {
    top: Piece,
    colors: Vec<Color>,
}

impl Stack {
    /// Creates a new [`Stack`].
    ///
    /// Specify the `top` piece of the stack and the `colors` of the pieces in the stack,
    /// given in order from bottom to top, including the color of the top piece.
    ///
    /// # Panics
    ///
    /// The constructor panics if the `colors` iterator is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Stack, Color, Piece, ParseTpsError};
    /// // In TPS this is a stack of a black capstone on top of a white flat.
    /// let stack: Stack = "12C".parse()?;
    ///
    /// let colors = vec![Color::White, Color::Black];
    /// assert_eq!(Stack::new(Piece::Cap, colors.into_iter()), stack);
    /// # Ok::<(), ParseTpsError>(())
    /// ```
    ///
    /// ```should_panic
    /// # use takparse::{Stack, Piece};
    /// Stack::new(Piece::Flat, [].into_iter()); // panics
    /// ```
    pub fn new<I: IntoIterator<Item = Color>>(top: Piece, colors: I) -> Self {
        let colors = Vec::from_iter(colors);
        assert!(!colors.is_empty());
        Self { top, colors }
    }

    /// Getter for `top`.
    pub fn top(&self) -> Piece {
        self.top
    }

    /// Getter for `colors`.
    /// Returns an iterator of owned `Color`s so you can easily iterate
    /// or use any collection you want, independent of how the colors are stored internally.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Stack, Color, ParseTpsError};
    /// let stack: Stack = "122C".parse()?;
    /// let colors: Vec<Color> = stack.colors().collect();
    /// assert_eq!(colors, vec![Color::White, Color::Black, Color::Black]);
    /// # Ok::<(), ParseTpsError>(())
    /// ```
    pub fn colors(&self) -> impl Iterator<Item = Color> + '_ {
        self.colors.iter().copied()
    }

    /// Get the color of the top piece. This is the last color in `colors`.
    pub fn top_color(&self) -> Color {
        *self.colors.last().unwrap()
    }

    /// Get the color of the bottom piece. This is first color in `colors`.
    pub fn bottom_color(&self) -> Color {
        *self.colors.first().unwrap()
    }
}

impl FromStr for Stack {
    type Err = ParseTpsError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut top = Piece::Flat;
        let mut colors = vec![];

        let mut i = s.chars();
        while let Some(c) = i.next() {
            match c.to_string().parse() {
                Ok(color) => colors.push(color),
                _ => {
                    top = once(c)
                        .chain(i)
                        .collect::<String>()
                        .parse()
                        .map_err(|_| ParseTpsError::InvalidPiece)?;
                    break;
                }
            }
        }

        match colors.len() {
            0 => Err(ParseTpsError::MissingColorOfPiece),
            _ => Ok(Self { top, colors }),
        }
    }
}

impl Display for Stack {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        self.colors().try_for_each(|c| c.fmt(f))?;
        self.top().fmt(f)
    }
}

/// An entry in the TPS for a board position.
///
/// Can either be a stack or a line of empty squares.
/// This is because multiple empty squares can be written as one entry.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExtendedSquare {
    /// A square with a stack on it.
    Stack(Stack),
    /// Empty squares, where the contained value tells you how many.
    EmptySquares(usize),
}

impl ExtendedSquare {
    fn iter(&self) -> Iter {
        Iter::new(self)
    }
}

impl FromStr for ExtendedSquare {
    type Err = ParseTpsError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut i = s.chars();
        match i.next() {
            Some('x') => {
                let suffix: String = i.collect();
                let run_length = match suffix.parse::<usize>() {
                    Ok(c) => c,
                    Err(p) if *p.kind() == IntErrorKind::Empty => 1,
                    _ => return Err(ParseTpsError::InvalidRunLength),
                };
                Ok(ExtendedSquare::EmptySquares(run_length))
            }
            _ => s.parse().map(Self::Stack),
        }
    }
}

impl Display for ExtendedSquare {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Stack(s) => s.fmt(f),
            &Self::EmptySquares(count) => match count {
                1 => 'x'.fmt(f),
                _ => write!(f, "x{count}"),
            },
        }
    }
}

struct Iter<'a> {
    item: Option<&'a Stack>,
    count: usize,
}

impl<'a> Iter<'a> {
    pub fn new(es: &'a ExtendedSquare) -> Self {
        match es {
            ExtendedSquare::Stack(s) => Self {
                item: Some(s),
                count: 1,
            },
            &ExtendedSquare::EmptySquares(count) => Self { item: None, count },
        }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = Option<&'a Stack>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.count {
            0 => None,
            _ => {
                self.count -= 1;
                Some(self.item)
            }
        }
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.len()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<'a> ExactSizeIterator for Iter<'a> {
    fn len(&self) -> usize {
        self.count
    }
}

/* TODO: overhaul
 * board should be a 1d boxed slice
 * rename and retype color and full move
 * figure out constructor
 * fix ply
 */

/// Parsed TPS struct which has a one-to-one mapping with a TPS string.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Tps {
    board: Vec<Vec<ExtendedSquare>>,
    color: Color,
    full_move: NonZeroUsize,
}

impl Tps {
    /// Create a new [`Tps`].
    ///
    /// `board` is a collection of rows, where in each row you have an [`ExtendedSquare`].
    /// `active_player` is the player who's turn it is.
    /// `full_move_number` is the move number, starting at 1.
    ///
    /// No checks are performed with this constructor, so it is possible to create
    /// an invalid board state, such as when there are a different amount of columns in each row
    /// or when the number of columns does not match the number rows.
    ///
    /// This constructor will canonicalize the representation,
    /// which means it will join consecutive empty squares together.
    ///
    /// # Safety
    ///
    /// This function is perfectly safe at the moment.
    /// The reason for the `unsafe` is to reserve the possibility of having undefined behavior
    /// in the future when an invalid board state is passed in as input.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Tps, Stack, ExtendedSquare, Color, ParseTpsError};
    /// # use std::num::NonZeroUsize;
    /// let stack: Stack = "112C".parse()?;
    /// let board = vec![
    ///     vec![
    ///         ExtendedSquare::Stack(stack),
    ///         ExtendedSquare::EmptySquares(2),
    ///     ],
    ///     vec![ExtendedSquare::EmptySquares(3)],
    ///     vec![ExtendedSquare::EmptySquares(3)],
    /// ];
    /// let tps =
    ///     unsafe { Tps::new_unchecked(board, Color::Black, NonZeroUsize::new_unchecked(10)) };
    /// assert_eq!(tps, "112C,x2/x3/x3 2 10".parse()?);
    /// # Ok::<(), ParseTpsError>(())
    /// ```
    pub unsafe fn new_unchecked(
        mut board: Vec<Vec<ExtendedSquare>>,
        active_player: Color,
        full_move_number: NonZeroUsize,
    ) -> Self {
        canonicalize(&mut board);
        Self {
            board,
            color: active_player,
            full_move: full_move_number,
        }
    }

    /// Get an iterator over iterators of optional stacks.
    /// The outer iterator iterates over rows, the inner iterator iterates over squares.
    /// Each element in the inner iterator is an option, where [`None`] means the square is empty.
    /// The [`Some`] variant has a [`Stack`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Tps, ParseTpsError};
    /// let tps: Tps = "1,2,12S/2,x2/x2,211C 1 15".parse()?;
    /// for row in tps.board_2d() {
    ///     for square in row {
    ///         let out = match square {
    ///             Some(stack) => "stack",
    ///             None => "empty",
    ///         };
    ///         // prints stack, stack, stack, stack, empty, empty, empty, empty, stack
    ///         println!("{out}");
    ///     }
    /// }
    /// # Ok::<(), ParseTpsError>(())
    /// ```
    pub fn board_2d(&self) -> impl Iterator<Item = impl Iterator<Item = Option<&'_ Stack>>> {
        self.board
            .iter()
            .map(|row| row.iter().flat_map(ExtendedSquare::iter))
    }

    /// Get an iterator over the board. Each element is an option, where the [`None`]
    /// variant means the square is empty and the [`Some`] variant houses a [`Stack`].
    ///
    /// This function is just a flattened version of [`Tps::board_2d`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Tps, ParseTpsError};
    /// let tps: Tps = "1,2,12S/2,x2/x2,211C 1 15".parse()?;
    /// for square in tps.board() {
    ///     let out = match square {
    ///         Some(stack) => "stack",
    ///         None => "empty",
    ///     };
    ///     // prints stack, stack, stack, stack, empty, empty, empty, empty, stack
    ///     println!("{out}");
    /// }
    /// # Ok::<(), ParseTpsError>(())
    /// ```
    pub fn board(&self) -> impl Iterator<Item = Option<&'_ Stack>> {
        self.board_2d().flatten()
    }

    /// Get the size of the board.
    ///
    /// For board with 6 rows (normal 6x6 board), this returns 6.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Tps, ParseTpsError};
    /// let tps: Tps = "1,2,12S/2,x2/x2,211C 1 15".parse()?;
    /// assert_eq!(tps.size(), 3);
    /// # Ok::<(), ParseTpsError>(())
    /// ```
    pub fn size(&self) -> usize {
        self.board.len()
    }

    /// Getter for `color`.
    pub fn color(&self) -> Color {
        self.color
    }

    /// Getter for `full_move`.
    pub fn full_move(&self) -> usize {
        self.full_move.get()
    }

    /// Get the current ply.
    ///
    /// Plies are zero-indexed and increment each time a player makes a move.
    ///
    /// On turn one, the ply is 0 when it is white to move, and 1 when black is to move.
    /// On turn 10 it would be ply 18 on white's move, and 19 on black's move.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Tps, ParseTpsError};
    /// let tps: Tps = "x3/x3/x3 1 23".parse()?;
    /// assert_eq!(tps.ply(), 44);
    /// # Ok::<(), ParseTpsError>(())
    /// ```
    pub fn ply(&self) -> usize {
        (self.full_move() - 1) * 2
            + if let Color::White = self.color() {
                0
            } else {
                1
            }
    }

    /// Generate the [`Tps`] for a board of the given `size`.
    ///
    /// The starting position is all squares empty, turn 1, white to move.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Tps, ParseTpsError};
    /// assert_eq!(Tps::starting_position(4), "x4/x4/x4/x4 1 1".parse()?);
    /// # Ok::<(), ParseTpsError>(())
    /// ```
    pub fn starting_position(size: usize) -> Self {
        start_position_tps(size).parse().unwrap()
    }
}

fn start_position_tps(size: usize) -> String {
    let row = format!("x{size}");
    format!(
        "{} 1 1",
        repeat(row).take(size).collect::<Vec<_>>().join("/")
    )
}

fn canonicalize(board: &mut [Vec<ExtendedSquare>]) {
    board.iter_mut().for_each(|row| {
        row.dedup_by(|item, acc| {
            if let ExtendedSquare::EmptySquares(acc) = acc {
                if let ExtendedSquare::EmptySquares(item) = item {
                    *acc += *item;
                    return true;
                }
            }
            false
        });
        row.retain(|es| *es != ExtendedSquare::EmptySquares(0));
    });
}

impl FromStr for Tps {
    type Err = ParseTpsError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let segments: Vec<_> = s.split(' ').collect();

        let [board, color, full_move]: [_; 3] = segments[..]
            .try_into()
            .map_err(|_| ParseTpsError::WrongSegmentCount)?;

        let color = color.parse()?;
        let full_move = full_move
            .parse()
            .map_err(|_| ParseTpsError::InvalidFullMove)?;

        let board = if board.is_empty() {
            vec![]
        } else {
            let rows: Vec<_> = board.split('/').collect();
            let size = rows.len();

            let mut board = rows
                .into_iter()
                .map(|row| {
                    let row = row
                        .split(',')
                        .map(ExtendedSquare::from_str)
                        .collect::<Result<Vec<_>, _>>()?;

                    if row.iter().map(|es| es.iter().len()).sum::<usize>() == size {
                        Ok(row)
                    } else {
                        Err(ParseTpsError::NonSquareBoard)
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;

            canonicalize(&mut board);
            board
        };

        Ok(Tps {
            board,
            color,
            full_move,
        })
    }
}

impl Display for Tps {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let fmt_row = |row: &Vec<ExtendedSquare>, f: &mut Formatter<'_>| {
            if let Some(es) = row.get(0) {
                es.fmt(f)?;
                row[1..].iter().try_for_each(|es| write!(f, ",{es}"))
            } else {
                Ok(())
            }
        };

        if let Some(row) = self.board.get(0) {
            fmt_row(row, f)?;
            self.board[1..].iter().try_for_each(|row| {
                '/'.fmt(f)?;
                fmt_row(row, f)
            })?;
        }

        write!(f, " {} {}", self.color(), self.full_move())
    }
}

/// Error returned when something goes wrong during the parsing of a [`Tps`] string.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseTpsError {
    /// Returned when the string has an incorrect number of segments.
    /// Segments are sections separated by spaces. There should be 3 segments.
    WrongSegmentCount,
    /// Returned when the color of the player to move is missing.
    MissingColor,
    /// This variant is never returned.
    #[deprecated]
    MissingPiece,
    /// Returned if there is a piece specifier without a color.
    MissingColorOfPiece,
    /// Is the color in a stack is not '1' or '2' then this variant is used.
    InvalidColor,
    /// If the piece specifier is not 'S' or 'C' then this variant is used.
    InvalidPiece,
    /// Returned when the number after 'x' (i.e. how many empty squares) is invalid.
    InvalidRunLength,
    /// Returned when the move number is invalid.
    InvalidFullMove,
    /// When the numbers of rows and columns do not match, this variant is returned.
    NonSquareBoard,
}

impl Error for ParseTpsError {}

impl Display for ParseTpsError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use ParseTpsError::*;

        match *self {
            WrongSegmentCount => "found incorrect number of segments",
            MissingColor => "missing required color annotation",
            MissingPiece => "missing required piece annotation",
            MissingColorOfPiece => "piece missing required color annotation",
            InvalidColor => "found color other than \"1\" or \"2\"",
            InvalidPiece => "found piece other than \"S\" or \"C\"",
            InvalidRunLength => "malformed adjacent empty square count",
            InvalidFullMove => "malformed full move counter",
            NonSquareBoard => "length of board row different than column",
        }
        .fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cmp::PartialEq, fmt::Debug, iter::repeat, str::FromStr};
    use ParseTpsError::*;

    fn round_trip<
        'a,
        T: FromStr<Err = ParseTpsError> + Display + Debug,
        I: IntoIterator<Item = &'a str>,
    >(
        cases: I,
    ) {
        transform::<T, _>(cases.into_iter().map(|s| (s, s)));
    }

    fn transform<
        'a,
        T: FromStr<Err = ParseTpsError> + Display + Debug,
        I: IntoIterator<Item = (&'a str, &'a str)>,
    >(
        from_to_pairs: I,
    ) {
        from_to_pairs
            .into_iter()
            .for_each(|(from, to)| assert_eq!(from.parse::<T>().unwrap().to_string(), to));
    }

    fn error<
        'a,
        T: FromStr<Err = ParseTpsError> + PartialEq + Debug,
        I: IntoIterator<Item = &'a str>,
    >(
        cases: I,
        err: ParseTpsError,
    ) {
        cases
            .into_iter()
            .for_each(|s| assert_eq!(s.parse::<T>(), Err(err)));
    }

    #[test]
    fn color() {
        round_trip::<Color, _>(["1", "2"]);
    }

    #[test]
    fn not_color() {
        error::<Color, _>(
            ["3", "12", "white", "w", "W", "blarg", "ą", "I"],
            InvalidColor,
        );
        error::<Color, _>([""], MissingColor);
    }

    #[test]
    fn stack() {
        round_trip::<Stack, _>(["1", "2", "1S", "2C", "11211221", "22221C"]);
    }

    #[test]
    fn not_stack() {
        error::<Stack, _>(["123", "12P", "hi", "a", "1SC"], InvalidPiece);
        error::<Stack, _>(["", "S", "C"], MissingColorOfPiece);
    }

    #[test]
    fn ext_square() {
        round_trip::<ExtendedSquare, _>(["121S", "112", "x", "x0", "x4", "x213", "x1221"]);
        transform::<ExtendedSquare, _>([("x1", "x")]);
    }

    #[test]
    fn not_ext_square() {
        error::<ExtendedSquare, _>(["x_two", "xF", "xS", "x "], InvalidRunLength);
    }

    fn alt_start_position_tps(s: usize) -> String {
        let tile = "x";
        format!(
            "{} 1 1",
            repeat(repeat(tile).take(s).collect::<Vec<_>>().join(","))
                .take(s)
                .collect::<Vec<_>>()
                .join("/")
        )
    }

    #[test]
    fn standard_start_positions() {
        round_trip::<Tps, _>(
            (3..9)
                .map(start_position_tps)
                .collect::<Vec<_>>()
                .iter()
                .map(String::as_str),
        );
    }

    #[test]
    fn unopt_standard_start_positions() {
        transform::<Tps, _>(
            (3..9)
                .map(|s| (alt_start_position_tps(s), start_position_tps(s)))
                .collect::<Vec<_>>()
                .iter()
                .map(|(from, to)| (from.as_str(), to.as_str())),
        );
    }

    #[test]
    fn nonstandard_start_positions() {
        round_trip::<Tps, _>([" 1 1", "x2/x2 1 1"]);
        transform::<Tps, _>([("x1 1 1", "x 1 1")]);
    }

    #[test]
    fn tps() {
        transform::<Tps, _>([
            ("x3,x/x,x,x,x/x4/x,x2,x 1 1", "x4/x4/x4/x4 1 1"),
            (
                "1111C,x,2122212221122111S,x/1221,x0,x0,2F,x0,22C,212S/x2,x,x1/x,1S,x,x 2 40",
                "1111C,x,2122212221122111S,x/1221,2,22C,212S/x4/x,1S,x2 2 40",
            ),
        ])
    }

    #[test]
    fn not_tps() {
        error::<Tps, _>(
            ["", "x2/x2 1 1 ", " x2/x2 1 1", "1 4", "x2/x2 2"],
            WrongSegmentCount,
        );
        error::<Tps, _>(["x2/x2 w 1"], InvalidColor);
        error::<Tps, _>(["x2/x2 1 1.5"], InvalidFullMove);
        error::<Tps, _>(
            ["x/x 1 1", "x3/x3 1 1", "1,2,1C/x2/1112S,1S,x 1 9", "x0 1 1"],
            NonSquareBoard,
        );
    }
}
