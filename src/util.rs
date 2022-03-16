use std::{
    fmt::{Display, Formatter, Result as FmtResult},
    str::FromStr,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CanonicalPiece {
    Default,
    Flat,
    Wall,
    Cap,
}

impl FromStr for CanonicalPiece {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "" => Ok(Self::Default),
            "F" => Ok(Self::Flat),
            "S" => Ok(Self::Wall),
            "C" => Ok(Self::Cap),
            _ => Err(()),
        }
    }
}

impl Display for CanonicalPiece {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Default => "",
            Self::Flat => "F",
            Self::Wall => "S",
            Self::Cap => "C",
        }
        .fmt(f)
    }
}
