use std::{
    fmt::{Display, Formatter, Result as FmtResult},
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
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "" | "F" => Ok(Self::Flat),
            "S" => Ok(Self::Wall),
            "C" => Ok(Self::Cap),
            _ => Err(()),
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
