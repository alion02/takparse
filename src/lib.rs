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
        });
        row.retain(|es| !matches!(es, ExtendedSquare::EmptySquares(0)));
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

        let rows: Vec<_> = match board {
            "" => return Err(ParseTpsError::MissingBoard),
            _ => board.split('/').collect(),
        };
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
    MissingBoard,
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
            MissingBoard => "received \"\" as board",
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
    fn piece() {
        round_trip::<Piece, _>(["S", "C"]);
    }

    #[test]
    fn not_piece() {
        error::<Piece, _>(["1", "2", "F", "s", "c", "f", "thing"], InvalidPiece);
        error::<Piece, _>([""], MissingPiece);
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

    fn start_position_tps(s: usize) -> String {
        let row = format!("x{s}");
        format!("{} 1 1", repeat(row).take(s).collect::<Vec<_>>().join("/"))
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
        round_trip::<Tps, _>(["x2/x2 1 1"]);
        transform::<Tps, _>([("x1 1 1", "x 1 1")]);
    }

    #[test]
    fn tps() {
        transform::<Tps, _>([
            ("x3,x/x,x,x,x/x4/x,x2,x 1 1", "x4/x4/x4/x4 1 1"),
            (
                "1111C,x,2122212221122111S,x/1221,x0,x0,2,x0,22C,212S/x2,x,x1/x,1S,x,x 2 40",
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
        error::<Tps, _>([" 2 14"], MissingBoard);
        error::<Tps, _>(
            ["x/x 1 1", "x3/x3 1 1", "1,2,1C/x2/1112S,1S,x 1 9", "x0 1 1"],
            NonSquareBoard,
        );
    }
}
