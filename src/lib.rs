use std::{
    error::Error,
    fmt::{Display, Formatter, Result as FmtResult},
    iter::once,
    num::{IntErrorKind, NonZeroUsize},
    str::FromStr,
};

// TODO: serde, docs, tests

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Piece {
    Flat,
    Wall,
    Cap,
}

impl FromStr for Piece {
    type Err = ParseTpsError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "S" => Ok(Self::Wall),
            "C" => Ok(Self::Cap),
            "" => Err(ParseTpsError::MissingPiece),
            _ => Err(ParseTpsError::InvalidPiece),
        }
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
pub enum Color {
    White,
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Stack {
    top: Piece,
    colors: Vec<Color>,
}

impl Stack {
    pub fn top(&self) -> Piece {
        self.top
    }

    pub fn colors(&self) -> impl Iterator<Item = Color> + '_ {
        self.colors.iter().copied()
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
                    top = once(c).chain(i).collect::<String>().parse()?;
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
        self.colors().map(|c| c.fmt(f)).collect::<FmtResult>()?;
        self.top().fmt(f)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ExtendedSquare {
    Stack(Stack),
    EmptySquares(usize),
}

impl ExtendedSquare {
    pub fn iter(&self) -> Iter {
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
                _ => write!(f, "x{}", count),
            },
        }
    }
}

impl<'a> IntoIterator for &'a ExtendedSquare {
    type Item = Option<&'a Stack>;

    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Tps {
    board: Vec<Vec<ExtendedSquare>>,
    color: Color,
    full_move: NonZeroUsize,
}

impl Tps {
    pub fn board_2d(&self) -> impl Iterator<Item = impl Iterator<Item = Option<&'_ Stack>>> {
        self.board
            .iter()
            .map(|row| row.iter().flat_map(ExtendedSquare::iter))
    }

    pub fn board(&self) -> impl Iterator<Item = Option<&'_ Stack>> {
        self.board_2d().flatten()
    }

    pub fn size(&self) -> usize {
        self.board.len()
    }

    pub fn color(&self) -> Color {
        self.color
    }

    pub fn full_move(&self) -> usize {
        self.full_move.get()
    }

    pub fn ply(&self) -> usize {
        self.full_move() * 2
            + if let Color::White = self.color() {
                0
            } else {
                1
            }
    }
}

fn canonicalize(board: &mut Vec<Vec<ExtendedSquare>>) {
    board.iter_mut().for_each(|row| {
        row.dedup_by(|item, acc| {
            if let ExtendedSquare::EmptySquares(acc) = acc {
                if let ExtendedSquare::EmptySquares(item) = item {
                    *acc += *item;
                    return true;
                }
            }
            false
        })
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
                row[1..].iter().map(|es| write!(f, ",{es}")).collect()
            } else {
                Ok(())
            }
        };

        if let Some(row) = self.board.get(0) {
            fmt_row(row, f)?;
            self.board[1..]
                .iter()
                .map(|row| {
                    '/'.fmt(f)?;
                    fmt_row(row, f)
                })
                .collect::<FmtResult>()?;
        }

        write!(f, " {} {}", self.color(), self.full_move())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseTpsError {
    WrongSegmentCount,
    MissingColor,
    MissingPiece,
    MissingColorOfPiece,
    InvalidColor,
    InvalidPiece,
    InvalidRunLength,
    InvalidFullMove,
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
    use std::{fmt::Debug, str::FromStr};

    fn round_trip<T>(s: &str)
    where
        T: FromStr + Display,
        <T as FromStr>::Err: Debug,
    {
        transform::<T>(s, s);
    }

    fn transform<T>(from: &str, to: &str)
    where
        T: FromStr + Display,
        <T as FromStr>::Err: Debug,
    {
        assert_eq!(from.parse::<T>().unwrap().to_string(), to);
    }

    #[test]
    fn stack() {
        round_trip::<ExtendedSquare>("1121S");
    }

    #[test]
    fn flat_stack() {
        round_trip::<ExtendedSquare>("212211");
    }

    #[test]
    fn empty_squares() {
        round_trip::<ExtendedSquare>("x3");
    }

    #[test]
    fn one_empty_square() {
        round_trip::<ExtendedSquare>("x");
    }

    #[test]
    fn start_position() {
        round_trip::<Tps>("x5/x5/x5/x5/x5 1 1");
    }

    #[test]
    fn unoptimized_start_position() {
        transform::<Tps>("x,x,x/x,x,x/x,x,x 1 1", "x3/x3/x3 1 1");
    }

    #[test]
    fn partially_optimized_start_position() {
        transform::<Tps>("x3,x/x,x,x,x/x4/x,x2,x 1 1", "x4/x4/x4/x4 1 1");
    }

    #[test]
    fn weird_position() {
        transform::<Tps>(
            "1111C,x,2122212221122111S,x/1221,2,22C,212S/x2,x,x1/x,1S,x,x 2 40",
            "1111C,x,2122212221122111S,x/1221,2,22C,212S/x4/x,1S,x2 2 40",
        );
    }
}
