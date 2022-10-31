use chrono::{NaiveDate, NaiveTime};

use crate::{Color, Move, ParseMoveError, Tps};
use std::{
    error::Error,
    fmt::{Display, Formatter, Result as FmtResult},
    iter::once,
    str::FromStr,
};

/// PTN Tag which is used to add additional information to a PTN file.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Tag {
    key: String,
    value: String,
}

impl Tag {
    /// Create a new [`Tag`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::Tag;
    /// assert_eq!(Tag::new("Hello", "World").to_string(), "[Hello \"World\"]");
    /// assert_eq!(Tag::new("Size", "6").to_string(), "[Size \"6\"]");
    /// ```
    pub fn new<A: Into<String>, B: Into<String>>(key: A, value: B) -> Self {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    /// Getter for the `key`.
    pub fn key(&self) -> &str {
        &self.key
    }

    /// Getter for the `value`.
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl Display for Tag {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "[{} \"{}\"]", self.key, self.value)
    }
}

/// Error returned when something goes wrong during the parsing of a [`Tag`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseTagError {
    /// The tag is missing an opening square bracket '['.
    NoOpeningBracket,
    /// The tag is missing the first part of the tag, referred to as the key.
    MissingKey,
    /// Missing opening quotation marks '"' which enclose the value.
    NoOpeningQuotationMarks,
    /// An illegal escape was attempted in the value of the tag. The only allowed escapes are `\"` and `\\`.
    IllegalEscape,
    /// When the value is empty, this error is returned.
    MissingValue,
    /// Missing closing quotation marks '"' at the end of the value.
    NoClosingQuotationMarks,
    /// The tag is missing the closing square bracket ']'.
    NoClosingBracket,
    /// When there is text following after the value but before the closing square bracket, this error variant is returned.
    GarbageAfterValue,
    /// If there is text after the closing square bracket, this error variant is returned.
    GarbageAfterTag,
}

impl Error for ParseTagError {}

impl Display for ParseTagError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::NoOpeningBracket => "missing opening square bracket '[' at the start",
            Self::MissingKey => "missing key",
            Self::NoOpeningQuotationMarks => "missing opening quotation marks '\"' before value",
            Self::IllegalEscape => "invalid character found after a backslash-escape in the value",
            Self::MissingValue => "missing value",
            Self::NoClosingQuotationMarks => "missing closing quotation marks '\"' after value",
            Self::GarbageAfterValue => "non-whitespace text after closing quotation mark '\"'",
            Self::NoClosingBracket => "missing closing square bracket ']' at the end",
            Self::GarbageAfterTag => "text after the closing square bracket ']'",
        }
        .fmt(f)
    }
}

impl FromStr for Tag {
    type Err = ParseTagError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.chars();

        // open bracket
        let Some('[') = chars.next() else {Err(ParseTagError::NoOpeningBracket)?};

        // key
        let mut opened = false;
        let mut key = String::new();
        for c in chars.by_ref() {
            if c == '"' {
                opened = true;
                break;
            }
            key.push(c);
        }
        if !opened {
            Err(ParseTagError::NoOpeningQuotationMarks)?;
        }
        let key = key.trim();
        if key.is_empty() {
            Err(ParseTagError::MissingKey)?;
        }

        // value
        let mut value = String::new();
        let mut escape = false;
        let mut closed = false;
        for c in chars.by_ref() {
            if escape {
                match c {
                    '"' | '\\' => escape = false,
                    _ => Err(ParseTagError::IllegalEscape)?,
                }
            } else if c == '\\' {
                escape = true;
                continue;
            } else if c == '"' {
                closed = true;
                break;
            }

            value.push(c);
        }
        if !closed {
            Err(ParseTagError::NoClosingQuotationMarks)?;
        }
        if value.is_empty() {
            Err(ParseTagError::MissingValue)?;
        }

        // closing bracket
        let mut closed = false;
        for c in chars.by_ref() {
            if c == ']' {
                closed = true;
                break;
            }
            if !c.is_whitespace() {
                Err(ParseTagError::GarbageAfterValue)?;
            }
        }
        if !closed {
            Err(ParseTagError::NoClosingBracket)?;
        }
        if chars.count() != 0 {
            Err(ParseTagError::GarbageAfterTag)?
        }

        Ok(Self::new(key, value))
    }
}

/// The reason for a win in Tak.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum WinReason {
    /// The reason for the win was that one player made a road.
    Road,
    /// The reason for the win was that the game ended without a road, and one player had more flats.
    Flat,
    /// The `Other` variant should be used for anything that is not a road win or a flat win.
    /// Examples of `Other` are resignation and winning on time.
    #[default]
    Other,
}

impl Display for WinReason {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Road => "R",
            Self::Flat => "F",
            Self::Other => "1",
        }
        .fmt(f)
    }
}

/// The result of a game of Tak.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum GameResult {
    /// White (player 1) won the game.
    White(WinReason),
    /// Black (player 2) won the game.
    Black(WinReason),
    /// The players drew the game.
    #[default]
    Draw,
}

/// Error returned when something goes wrong during the parsing of a [`GameResult`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseGameResultError {
    /// The game result was not one of the valid and recognized formats.
    Invalid,
}

impl Display for ParseGameResultError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "invalid or unknown game result")
    }
}

impl Error for ParseGameResultError {}

impl Display for GameResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::White(reason) => write!(f, "{reason}-0"),
            Self::Black(reason) => write!(f, "0-{reason}"),
            Self::Draw => write!(f, "1/2-1/2"),
        }
    }
}

impl FromStr for GameResult {
    type Err = ParseGameResultError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "F-0" => GameResult::White(WinReason::Flat),
            "R-0" => GameResult::White(WinReason::Road),
            "1-0" => GameResult::White(WinReason::Other),
            "0-F" => GameResult::Black(WinReason::Flat),
            "0-R" => GameResult::Black(WinReason::Road),
            "0-1" => GameResult::Black(WinReason::Other),
            "1/2-1/2" => GameResult::Draw,
            _ => Err(ParseGameResultError::Invalid)?,
        })
    }
}

/// A PTN file which is used to document a game of Tak.
///
/// It includes tags which have extra information such as the size of the board.
/// Next it has a sequence of moves with optional comments.
/// Finally, if the game has ended, it includes the game result after the moves.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Ptn {
    tags: Vec<Tag>,
    moves: Vec<Move>,
    comments: Vec<Vec<String>>,
    result: Option<GameResult>,
}

impl Ptn {
    /// Create a new [`Ptn`].
    ///
    /// - `tags` is a collection of tags. Validity or repeated tags are not checked. If there is a `[TPS "<some valid tps>"]` tag
    ///   then it will be used for the display of the PTN file. The TPS determines which player starts and what the move number is.
    /// - `moves` is a collection of moves in the game. Again, validity of the move sequence is not checked.
    /// - `comments` is a collection of comment groups. Each comment group can contain multiple individual comments.
    ///   the group at index 0 contains comments about the game as a whole. Each group after that is tied to a move.
    ///   For example, the 4th ply would have comments at index 4.
    /// - `result` is the result of the game if it ended.
    ///
    /// # Panics
    ///
    /// Panics if the comments do not have a length of moves length + 1.
    /// This is because there is a comment group for each move,
    /// and also comments for the whole game which are at index 0.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Ptn, ParseMoveError, Tag};
    /// let ptn = Ptn::new(
    ///     vec![Tag::new("Size", "6")],
    ///     vec!["a6".parse()?, "a5".parse()?, "b5".parse()?],
    ///     vec![vec!["Cool Game".into()], vec![], vec!["The Hug".into()], vec![]],
    ///     None,
    /// );
    /// assert_eq!(ptn.to_string(), "[Size \"6\"]\n\n{Cool Game}\n1. a6 a5 {The Hug}\n2. b5\n");
    /// # Ok::<(), ParseMoveError>(())
    /// ```
    ///
    /// ```
    /// # use takparse::{Ptn, ParseMoveError, Tag};
    /// let ptn = Ptn::new(
    ///     vec![Tag::new("TPS", r#"2,x5/x6/x6/x4,1,x/x6/x5,1 2 2"#)],
    ///     vec!["c4".parse()?, "d3".parse()?],
    ///     vec![vec!["Opposite Corners".into(), "Knight's Move".into()], vec!["Centre Square".into()], vec![]],
    ///     None,
    /// );
    /// assert_eq!(
    ///     ptn.to_string(),
    ///     "[TPS \"2,x5/x6/x6/x4,1,x/x6/x5,1 2 2\"]\n\n{Opposite Corners} {Knight's Move}\n2. -- c4 {Centre Square}\n3. d3\n"
    /// );
    /// # Ok::<(), ParseMoveError>(())
    /// ```
    ///
    /// ```should_panic
    /// # use takparse::Ptn;
    /// Ptn::new(vec![], vec![], vec![], None); // panics because `comments.len() != moves.len() + 1`
    /// ```
    pub fn new(
        tags: Vec<Tag>,
        moves: Vec<Move>,
        comments: Vec<Vec<String>>,
        result: Option<GameResult>,
    ) -> Self {
        assert!(comments.len() == moves.len() + 1);
        Self {
            tags,
            moves,
            comments,
            result,
        }
    }

    /// Getter for `tags`.
    pub fn tags(&self) -> &[Tag] {
        &self.tags
    }

    /// Getter for `moves`.
    pub fn moves(&self) -> &[Move] {
        &self.moves
    }

    /// Getter for `comments`.
    pub fn comments(&self) -> &[Vec<String>] {
        &self.comments
    }

    /// Get the first matching tag's value.
    /// If the tag is not found [`None`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Ptn, ParseMoveError, Tag};
    /// let ptn = Ptn::new(
    ///     vec![
    ///         Tag::new("TPS", r#"2,x5/x6/x6/x4,1,x/x6/x5,1 2 2"#),
    ///         Tag::new("Size", "6"),
    ///         Tag::new("Size", "5"),
    ///     ],
    ///     vec!["c4".parse()?, "d3".parse()?],
    ///     vec![vec!["Opposite Corners".into(), "Knight's Move".into()], vec!["Centre Square".into()], vec![]],
    ///     None,
    /// );
    ///
    /// assert_eq!(ptn.get_tag("TPS"),  Some("2,x5/x6/x6/x4,1,x/x6/x5,1 2 2"));
    /// assert_eq!(ptn.get_tag("Size"), Some("6"));
    /// assert_eq!(ptn.get_tag("Foo"), None);
    /// # Ok::<(), ParseMoveError>(())
    /// ```
    pub fn get_tag(&self, key: &str) -> Option<&str> {
        for tag in &self.tags {
            if tag.key() == key {
                return Some(tag.value());
            }
        }
        None
    }

    /// Search for a tag with the key `Site` and return the value.
    /// If the tag is not found [`None`] is returned.
    pub fn site(&self) -> Option<&str> {
        self.get_tag("Site")
    }

    /// Search for a tag with the key `Event` and return the value.
    /// If the tag is not found [`None`] is returned.
    pub fn event(&self) -> Option<&str> {
        self.get_tag("Event")
    }

    /// Search for a tag with the key `Date` and return the value, parsed into a [`chrono::NaiveDate`] struct.
    /// If the tag is not found or parsing fails [`None`] is returned.
    ///
    /// The date should be in the format `YYYY.MM.DD`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Ptn, Tag};
    /// # use chrono::NaiveDate;
    /// let ptn = Ptn::new(vec![Tag::new("Date", "2022.11.01")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.date(), Some(NaiveDate::from_ymd(2022, 11, 01)));
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Date", "Invalid Date")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.date(), None);
    ///
    /// let ptn = Ptn::new(vec![Tag::new("NotDate", "Whatever")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.date(), None);
    /// ```
    pub fn date(&self) -> Option<NaiveDate> {
        let s = self.get_tag("Date")?;
        let mut split = s.split('.');
        let year = split.next()?.parse().ok()?;
        let month = split.next()?.parse().ok()?;
        let day = split.next()?.parse().ok()?;
        if split.next().is_some() {
            return None;
        };
        NaiveDate::from_ymd_opt(year, month, day)
    }

    /// Search for a tag with the key `Time` and return the value, parsed into a [`chrono::NaiveTime`] struct.
    /// If the tag is not found or parsing fails [`None`] is returned.
    ///
    /// The time should be in the format `HH:MM:SS`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Ptn, Tag};
    /// # use chrono::NaiveTime;
    /// let ptn = Ptn::new(vec![Tag::new("Time", "18:29:30")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.time(), Some(NaiveTime::from_hms(18, 29, 30)));
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Time", "Invalid Time")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.time(), None);
    ///
    /// let ptn = Ptn::new(vec![Tag::new("NotTime", "Whatever")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.time(), None);
    /// ```
    pub fn time(&self) -> Option<NaiveTime> {
        let s = self.get_tag("Time")?;
        let mut split = s.split(':');
        let hour = split.next()?.parse().ok()?;
        let min = split.next()?.parse().ok()?;
        let sec = split.next()?.parse().ok()?;
        if split.next().is_some() {
            return None;
        };
        NaiveTime::from_hms_opt(hour, min, sec)
    }

    /// Search for a tag with the key `Player1` and return the value.
    /// This is the name of the player playing as white.
    /// If the tag is not found [`None`] is returned.
    pub fn player_1(&self) -> Option<&str> {
        self.get_tag("Player1")
    }

    /// Search for a tag with the key `Player2` and return the value.
    /// This is the name of the player playing as black.
    /// If the tag is not found [`None`] is returned.
    pub fn player_2(&self) -> Option<&str> {
        self.get_tag("Player2")
    }

    /// Search for a tag with the key `Rating1` and return the value, parsed as an integer.
    /// This gets the rating of the player playing as white.
    /// If the tag is not found [`None`] is returned.
    pub fn rating_1(&self) -> Option<i32> {
        self.get_tag("Rating1")?.parse().ok()
    }

    /// Search for a tag with the key `Rating2` and return the value, parsed as an integer.
    /// This gets the rating of the player playing as black.
    /// If the tag is not found [`None`] is returned.
    pub fn rating_2(&self) -> Option<i32> {
        self.get_tag("Rating2")?.parse().ok()
    }

    /// Search for a tag with the key `Clock` and return the value.
    ///
    /// This is used to tell us the time controls used for the game.
    /// It is not parsed because a standard format is not specified.
    /// If the tag is not found [`None`] is returned.
    pub fn clock(&self) -> Option<&str> {
        self.get_tag("Clock")
    }

    /// Search for the tag with the key `Opening` and return the value.
    /// If the tag is not found [`None`] is returned.
    pub fn opening(&self) -> Option<&str> {
        self.get_tag("Opening")
    }

    /// Get the result of the game.
    ///
    /// If the result is already stored in the [`Ptn`] struct then that is returned.
    /// Otherwise, search for the tag with the key `Result` and return the value, parsed as a [`GameResult`].
    /// If there is no stored result and tag is not found or parsing of the value fails then [`None`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Ptn, Tag};
    /// let ptn = Ptn::new(vec![], vec![], vec![vec![]], "F-0".parse().ok());
    /// assert_eq!(ptn.result(), "F-0".parse().ok());
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Result", "0-R")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.result(), "0-R".parse().ok());
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Result", "0-R")], vec![], vec![vec![]], "F-0".parse().ok());
    /// assert_eq!(ptn.result(), "F-0".parse().ok());
    ///
    /// let ptn = Ptn::new(vec![], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.result(), None);
    /// ```
    pub fn result(&self) -> Option<GameResult> {
        if self.result.is_some() {
            return self.result;
        }
        self.get_tag("Result")?.parse().ok()
    }

    /// Search for a tag with the key `Size` and return the value, parsed as an integer.
    /// This is the size of the board. One of the few mandatory tags for a valid PTN.
    /// If the tag is not found or parsing fails [`None`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Ptn, Tag};
    /// let ptn = Ptn::new(vec![Tag::new("Size", "5")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.size(), Some(5));
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Size", "Five")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.time(), None);
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Largeness", "123")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.time(), None);
    /// ```
    pub fn size(&self) -> Option<usize> {
        self.get_tag("Size")?.parse().ok()
    }

    /// Get the komi of the game as an integer. This rounds fractional komi down.
    ///
    /// It works by searching for a tag with the key `Komi`, parsing the value as half-komi,
    /// and then returning half of that.
    /// If the tag is not found or parsing fails [`None`] is returned.
    ///
    /// ```
    /// # use takparse::{Ptn, Tag};
    /// let ptn = Ptn::new(vec![Tag::new("Komi", "2")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.komi(), Some(2));
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Komi", "2.5")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.komi(), Some(2));
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Komi", "-0.5")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.komi(), Some(0));
    /// ```
    pub fn komi(&self) -> Option<i32> {
        self.half_komi().map(|x| x / 2)
    }

    /// Get the half-komi for a game. Half-komi is twice the komi value.
    /// It is used because komi can also be fractional when we want to eliminate draws.
    ///
    /// Allowed values for komi are in one of these formats:
    /// - `<integer>`
    /// - `<integer>.5`
    /// - `<integer>.0`
    ///
    /// This method searches for a tag with the key `Komi`.
    /// If the tag is not found or parsing fails [`None`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Ptn, Tag};
    /// let ptn = Ptn::new(vec![Tag::new("Komi", "2")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.half_komi(), Some(4));
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Komi", "2.5")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.half_komi(), Some(5));
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Komi", "-0.5")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.half_komi(), Some(-1));
    /// ```
    pub fn half_komi(&self) -> Option<i32> {
        let s = self.get_tag("Komi")?;

        match s.split_once('.') {
            None => s.parse::<i32>().ok().map(|x| x * 2),
            Some((whole, frac)) => {
                let minus = s.get(..1)? == "-";
                let whole = whole.parse::<i32>().ok()?;
                match frac {
                    "" | "0" => Some(2 * whole),
                    "5" => Some(2 * whole + if minus { -1 } else { 1 }),
                    _ => None,
                }
            }
        }
    }

    /// Search for a tag with the key `Flats` and return the value, parsed as an integer.
    /// If the tag is not found or parsing fails [`None`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Ptn, Tag};
    /// let ptn = Ptn::new(vec![Tag::new("Flats", "30")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.flats(), Some(30));
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Flats", "-123")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.flats(), None);
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Fs", "1")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.flats(), None);
    /// ```
    pub fn flats(&self) -> Option<u32> {
        self.get_tag("Flats")?.parse().ok()
    }

    /// Search for a tag with the key `Caps` and return the value, parsed as an integer.
    /// If the tag is not found or parsing fails [`None`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Ptn, Tag};
    /// let ptn = Ptn::new(vec![Tag::new("Caps", "1")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.caps(), Some(1));
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Caps", "-1")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.caps(), None);
    ///
    /// let ptn = Ptn::new(vec![Tag::new("Capstones", "1")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.caps(), None);
    /// ```
    pub fn caps(&self) -> Option<u32> {
        self.get_tag("Caps")?.parse().ok()
    }

    /// Search for a tag with the key `TPS` and return the value, parsed as a [`Tps`] struct.
    /// If the tag is not found or parsing fails [`None`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use takparse::{Ptn, Tag};
    /// let ptn = Ptn::new(vec![Tag::new("TPS", "2,x5/x6/x2,2,x3/x3,1,1,x/x6/x5,1 2 3")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.tps(), "2,x5/x6/x2,2,x3/x3,1,1,x/x6/x5,1 2 3".parse().ok());
    ///
    /// let ptn = Ptn::new(vec![Tag::new("TPS", "invalid")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.tps(), None);
    ///
    /// let ptn = Ptn::new(vec![Tag::new("TeePeeEs", ":)")], vec![], vec![vec![]], None);
    /// assert_eq!(ptn.tps(), None);
    /// ```
    pub fn tps(&self) -> Option<Tps> {
        self.get_tag("TPS")?.parse().ok()
    }
}

impl Display for Ptn {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        // Display tags.
        for tag in &self.tags {
            writeln!(f, "{tag}")?;
        }

        // Display game comments.
        let mut comment_groups = self.comments.iter();
        if let Some(game_comments) = comment_groups.next() {
            if !game_comments.is_empty() {
                write!(f, "\n{{{}}}", game_comments.join("} {"))?;
            }
        }

        // Helper function for joining comment groups together.
        fn format_comments(comments: &Vec<String>) -> String {
            if comments.is_empty() {
                "".into()
            } else {
                format!(" {{{}}}", comments.join("} {"))
            }
        }

        let mut moves = self.moves.iter();
        let mut turn = 1;

        // Starting from TPS.
        if let Some(tps) = self.tps() {
            turn = tps.full_move();
            // Starting as black.
            if tps.color() == Color::Black {
                if let Some(black) = moves.next() {
                    let black_comments = format_comments(comment_groups.next().unwrap());
                    write!(f, "\n{turn}. -- {black}{black_comments}")?;
                    turn += 1;
                }
            }
        }

        // Display moves.
        while let Some(white) = moves.next() {
            let white_comments = format_comments(comment_groups.next().unwrap());
            if let Some(black) = moves.next() {
                let black_comments = format_comments(comment_groups.next().unwrap());
                write!(
                    f,
                    "\n{turn}. {white}{white_comments} {black}{black_comments}"
                )?;
            } else {
                write!(f, "\n{turn}. {white}{white_comments}")?;
                break;
            }
            turn += 1;
        }

        // Display game result.
        if let Some(result) = self.result {
            writeln!(f, " {result}")
        } else {
            writeln!(f)
        }
    }
}

/// Error returned when something goes wrong during the parsing of a [`Ptn`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParsePtnError {
    /// Wrapper variant for [`ParseTagError`]. Returned if something is wrong with a tag.
    Tag(ParseTagError),
    /// Wrapper variant for [`ParseMoveError`]. Returned if there is an issue with one of the moves.
    Move(ParseMoveError),
    /// Returned when the Ptn ends with a number without a dot. This kind of error is not returned
    /// if there is an issue with the move numbers in the middle of the PTN. Instead that number will parsed as a move,
    /// and if it is not a valid move, then the `Move` variant of this error will be returned instead.
    IncompleteMoveNum,
    /// Returned when the PTN ends while still in comment mode. This happens if a comment is opened, but not closed.
    UnclosedComment,
    /// Returned if there is non-whitespace text after a game result.
    GarbageAfterResult,
}

impl Display for ParsePtnError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use ParsePtnError::*;
        match self {
            Tag(err) => err.fmt(f),
            Move(err) => err.fmt(f),
            IncompleteMoveNum => "PTN ended with an incomplete move number".fmt(f),
            UnclosedComment => "PTN ended while in still in comment".fmt(f),
            GarbageAfterResult => "non whitespace after game result is not allowed".fmt(f),
        }
    }
}

impl Error for ParsePtnError {}

impl From<ParseTagError> for ParsePtnError {
    fn from(value: ParseTagError) -> Self {
        Self::Tag(value)
    }
}

impl From<ParseMoveError> for ParsePtnError {
    fn from(value: ParseMoveError) -> Self {
        Self::Move(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParsePtnTagState {
    NotInTag,
    Start,
    Value,
    Escape,
    End,
    Moves,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParsePtnMovesState {
    Outside,
    MoveNum,
    Move,
    Comment,
}

impl FromStr for Ptn {
    type Err = ParsePtnError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.chars();

        // Parse tags.
        let mut tags = Vec::new();
        let mut state = ParsePtnTagState::NotInTag;
        let mut tag = String::new();
        let mut last_char = None;
        for c in chars.by_ref() {
            use ParsePtnTagState::*;
            // state transition table
            state = match (state, c) {
                (NotInTag, '[') => Start,
                (Start, '"') => Value,
                (Value, '\\') => Escape,
                (Escape, _) => Value,
                (Value, '"') => End,
                (End, ']') => NotInTag,
                (NotInTag, c) if !c.is_whitespace() => Moves,
                (state, _) => state,
            };
            // state action table
            match state {
                Start | Value | Escape | End => tag.push(c),
                NotInTag => {
                    // just finished tag
                    if c == ']' {
                        tag.push(c);
                        tags.push(std::mem::take(&mut tag).parse()?);
                    }
                }
                Moves => {
                    last_char = Some(c);
                    break;
                }
            };
        }
        // End of string.
        if last_char.is_none() {
            if state != ParsePtnTagState::NotInTag {
                tags.push(tag.parse()?);
            }
            return Ok(Self::new(tags, Vec::new(), vec![Vec::new()], None));
        }

        // Parse moves.
        let mut moves = Vec::new();
        let mut comments = Vec::new();
        let mut result = None;
        let mut state = ParsePtnMovesState::Outside;
        let mut comment_group = Vec::new();
        let mut chunk = String::new();
        for c in once(last_char.unwrap()).chain(chars.by_ref()) {
            use ParsePtnMovesState::*;
            // state transition table
            let new_state = match (state, c) {
                (Outside | Move, '{') => Comment,
                (Outside, '0'..='9') => MoveNum,
                (Outside, c) if c != '-' && !c.is_whitespace() => Move,
                (MoveNum, '.') => Outside,
                (MoveNum, '0'..='9') => MoveNum,
                (MoveNum, _) => Move,
                (Comment, '}') => Outside,
                (Move, c) if c.is_whitespace() => Outside,
                (state, _) => state,
            };

            // state action-on-transition table
            match (state, new_state) {
                (Comment, Outside) => {
                    // Add finished comment to comment group.
                    comment_group.push(std::mem::take(&mut chunk));
                }
                (MoveNum, Outside) => {
                    // We just completely disregard move numbers.
                    chunk.clear();
                }
                (Move, Outside | Comment) => {
                    // Try parsing game result.
                    if let Ok(game_result) = chunk.parse::<GameResult>() {
                        result = Some(game_result);
                        break;
                    }
                    // Push comment group for previous move.
                    comments.push(std::mem::take(&mut comment_group));
                    moves.push(std::mem::take(&mut chunk).parse()?);
                }
                (Move | MoveNum | Comment, _) | (_, Move | MoveNum) => {
                    chunk.push(c);
                }
                _ => {}
            }
            state = new_state;
        }
        // If we ran out of characters.
        match state {
            ParsePtnMovesState::Move => {
                // Try parsing game result.
                if let Ok(game_result) = chunk.parse::<GameResult>() {
                    result = Some(game_result);
                } else {
                    // Push comment group for previous move.
                    comments.push(std::mem::take(&mut comment_group));
                    // Push last move.
                    moves.push(chunk.parse()?);
                }
            }
            ParsePtnMovesState::MoveNum => Err(ParsePtnError::IncompleteMoveNum)?,
            ParsePtnMovesState::Comment => Err(ParsePtnError::UnclosedComment)?,
            ParsePtnMovesState::Outside => {}
        }
        // Only whitespace allowed after game result.
        if chars.skip_while(|c| c.is_whitespace()).count() != 0 {
            Err(ParsePtnError::GarbageAfterResult)?;
        }
        // Push last comment group.
        comments.push(comment_group);

        Ok(Self::new(tags, moves, comments, result))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::*;

    #[test]
    fn happy_tags() {
        assert_eq!(
            r#"[Site "PlayTak.com"]"#.parse(),
            Ok(Tag::new("Site", "PlayTak.com"))
        );
        assert_eq!(
            r#"[Event "Online Play"]"#.parse(),
            Ok(Tag::new("Event", "Online Play"))
        );
        assert_eq!(
            r#"[Date "2018.10.28"]"#.parse(),
            Ok(Tag::new("Date", "2018.10.28"))
        );
        assert_eq!(
            r#"[Time "16:10:44"]"#.parse(),
            Ok(Tag::new("Time", "16:10:44"))
        );
        assert_eq!(
            r#"[Player1 "FooBar"]"#.parse(),
            Ok(Tag::new("Player1", "FooBar"))
        );
        assert_eq!(
            r#"[Player2 "abc1234"]"#.parse(),
            Ok(Tag::new("Player2", "abc1234"))
        );
        assert_eq!(
            r#"[Clock "10:0 +20"]"#.parse(),
            Ok(Tag::new("Clock", "10:0 +20"))
        );
        assert_eq!(r#"[Result "R-0"]"#.parse(), Ok(Tag::new("Result", "R-0")));
        assert_eq!(r#"[Size "6"]"#.parse(), Ok(Tag::new("Size", "6")));
        assert_eq!(r#"[Komi "2"]"#.parse(), Ok(Tag::new("Komi", "2")));
    }

    #[test]
    fn unconventional_but_still_ok_tags() {
        assert_eq!(
            r#"[noSpace"between value and key"]"#.parse(),
            Ok(Tag::new("noSpace", "between value and key"))
        );
        assert_eq!(
            r#"[brackets "Ins[ide]The]Va[lue"]"#.parse(),
            Ok(Tag::new("brackets", "Ins[ide]The]Va[lue"))
        );
        assert_eq!(
            r#"[hell[[][[[[ "[]][[][]"]"#.parse(),
            Ok(Tag::new("hell[[][[[[", "[]][[][]"))
        );
        assert_eq!(
            r#"[\e\s\\c\ap\e\\ "\\\\\"\\\""]"#.parse(),
            Ok(Tag::new(r#"\e\s\\c\ap\e\\"#, "\\\\\"\\\""))
        );
        assert_eq!(
            r#"[  lots of space     "room to breathe"    ]"#.parse(),
            Ok(Tag::new("lots of space", "room to breathe"))
        );
        assert_eq!(
            r#"[ !_%#@ [($ )#@]\" \\\"\"]][] " ]"#.parse(),
            Ok(Tag::new(r#"!_%#@ [($ )#@]\"#, " \\\"\"]][] "))
        );
    }

    #[test]
    fn erroneous_tags() {
        error::<Tag, _, _>(
            [r#"abcd "hi"]"#, r#" [space "before"]"#, ""],
            ParseTagError::NoOpeningBracket,
        );
        error::<Tag, _, _>(
            [r#"[""]"#, r#"["value"]"#, r#"[   "value"]"#],
            ParseTagError::MissingKey,
        );
        error::<Tag, _, _>(
            ["[hello]", "[[][]]", "[hello world]"],
            ParseTagError::NoOpeningQuotationMarks,
        );
        error::<Tag, _, _>(
            [
                r#"[key "\ "]"#,
                r#"[key "\]"]"#,
                r#"[key "\["]"#,
                r#"[key "\a"]"#,
                r#"[key "\\ \'"]"#,
                r#"[key "\" \n"]"#,
            ],
            ParseTagError::IllegalEscape,
        );
        error::<Tag, _, _>(
            [r#"[key ""]"#, r#"[ key\"" ]"#, r#"[key "" "hi"]"#],
            ParseTagError::MissingValue,
        );
        error::<Tag, _, _>(
            [
                r#"[key "]"#,
                r#"[key "hello   ]"#,
                r#"[key "\" value]]"#,
                r#"[key "\" value\\\"]]"#,
            ],
            ParseTagError::NoClosingQuotationMarks,
        );
        error::<Tag, _, _>(
            [
                r#"[key "value""#,
                r#"[key "value\"]" "#,
                r#"[key] "value\"]]\\"  "#,
            ],
            ParseTagError::NoClosingBracket,
        );
        error::<Tag, _, _>(
            [
                r#"[key "value" hi]"#,
                r#"[key "value" \"\]]"#,
                r#"[key "value" \n"]"#,
            ],
            ParseTagError::GarbageAfterValue,
        );
        error::<Tag, _, _>(
            [
                r#"[key "value"]]"#,
                r#"[key "value"] "#,
                r#"[key "value"] hi there"#,
                r#"[key "value"] hi there]"#,
            ],
            ParseTagError::GarbageAfterTag,
        );
    }

    #[test]
    fn transform_whitespace_in_tags() {
        transform::<Tag, _, _>([
            (r#"[key "value"]"#, r#"[key "value"]"#),
            (r#"[ space "before"]"#, r#"[space "before"]"#),
            (r#"[no"space"]"#, r#"[no "space"]"#),
            (r#"[space "after" ]"#, r#"[space "after"]"#),
            (
                r#"[   very   spacious   "and  wasteful"    ]"#,
                r#"[very   spacious "and  wasteful"]"#,
            ),
        ])
    }

    #[test]
    fn happy_ptn() {
        let ptn = r#"
            [Site "PlayTak . com"]
            [Event "Online Play"]
            [Date "2018.10.28"]
            [Time "16:10:44"]
            [Player1 "aaaa"]
            [Player2 "bbbb"]
            [Clock "10:0 +20"]
            [Result "R-0"]
            [Size "6"]

            1. a6 f6
            2. d4 c4
            3. d3 c3
            4. d5 c5
            5. d2 Ce4
            6. c2 e3
            7. e2 b2
            8. Cb3 1e4<1
            9. 1d3<1 Sd1
            10. a3 1d1+1
        "#;
        let moves = vec![
            "a6", "f6", "d4", "c4", "d3", "c3", "d5", "c5", "d2", "Ce4", "c2", "e3", "e2", "b2",
            "Cb3", "1e4<1", "1d3<1", "Sd1", "a3", "1d1+1",
        ];
        let comment_groups = (0..(moves.len() + 1)).map(|_| Vec::new()).collect();
        assert_eq!(
            ptn.parse::<Ptn>().unwrap(),
            Ptn::new(
                vec![
                    Tag::new("Site", "PlayTak . com"),
                    Tag::new("Event", "Online Play"),
                    Tag::new("Date", "2018.10.28"),
                    Tag::new("Time", "16:10:44"),
                    Tag::new("Player1", "aaaa"),
                    Tag::new("Player2", "bbbb"),
                    Tag::new("Clock", "10:0 +20"),
                    Tag::new("Result", "R-0"),
                    Tag::new("Size", "6"),
                ],
                moves
                    .into_iter()
                    .map(|m| m.parse::<Move>())
                    .collect::<Result<_, _>>()
                    .unwrap(),
                comment_groups,
                None,
            )
        );
    }

    #[test]
    fn ugly_tags() {
        let ptn = r#"
            [Site "PlayTak dot com"] [Event "Online Play"][Date "2018.10.28"] [][[]] "]]]]\\\""]
        "#;
        assert_eq!(
            ptn.parse::<Ptn>().unwrap(),
            Ptn::new(
                vec![
                    Tag::new("Site", "PlayTak dot com"),
                    Tag::new("Event", "Online Play"),
                    Tag::new("Date", "2018.10.28"),
                    Tag::new("][[]]", "]]]]\\\""),
                ],
                vec![],
                vec![vec![]],
                None,
            )
        );
    }

    #[test]
    fn comments_everywhere() {
        let ptn = r#"
            [Size "6"] {[valid "tag"]} {a} 1. {b} {cd} a6 {ef} {{{{} f6 {aww man}2.{x}d4{y}c4
            {}3.{}d3{}{hello}{}c3
            4.d5{}c5
            {well} {this}5. {is}d2{quite} {strange}Ce4{don't you think} {  }
            6. c2 e3
            {at end}
        "#;
        assert_eq!(
            ptn.parse::<Ptn>().unwrap(),
            Ptn::new(
                vec![Tag::new("Size", "6"),],
                vec!["a6", "f6", "d4", "c4", "d3", "c3", "d5", "c5", "d2", "Ce4", "c2", "e3",]
                    .into_iter()
                    .map(|m| m.parse::<Move>())
                    .collect::<Result<_, _>>()
                    .unwrap(),
                vec![
                    vec![
                        "[valid \"tag\"]".into(),
                        "a".into(),
                        "b".into(),
                        "cd".into()
                    ],
                    vec!["ef".into(), "{{{".into()],
                    vec!["aww man".into(), "x".into()],
                    vec!["y".into()],
                    vec!["".into(), "".into()],
                    vec!["".into(), "hello".into(), "".into()],
                    vec![],
                    vec!["".into()],
                    vec!["well".into(), "this".into(), "is".into()],
                    vec!["quite".into(), "strange".into()],
                    vec!["don't you think".into(), "  ".into()],
                    vec![],
                    vec!["at end".into()],
                ],
                None,
            )
        );
    }

    #[test]
    fn without_move_numbers() {
        let ptn = r#"[Player1 "a"][Player2 "b"][Size "6"][Komi "0"][Opening "no-swap"] a3 a2 a3- b2 d4 {hi} b3?? b4!! c4!? c3 b5 a4 a3 c5 b6 d4< a5 c6 a3- Sa3"#;
        let moves = vec![
            "a3", "a2", "a3-", "b2", "d4", "b3", "b4", "c4", "c3", "b5", "a4", "a3", "c5", "b6",
            "d4<", "a5", "c6", "a3-", "Sa3",
        ];
        let mut comment_groups: Vec<Vec<String>> =
            (0..(moves.len() + 1)).map(|_| Vec::new()).collect();
        comment_groups[5].push("hi".into());
        assert_eq!(
            ptn.parse::<Ptn>().unwrap(),
            Ptn::new(
                vec![
                    Tag::new("Player1", "a"),
                    Tag::new("Player2", "b"),
                    Tag::new("Size", "6"),
                    Tag::new("Komi", "0"),
                    Tag::new("Opening", "no-swap")
                ],
                moves
                    .into_iter()
                    .map(|m| m.parse::<Move>())
                    .collect::<Result<_, _>>()
                    .unwrap(),
                comment_groups,
                None,
            )
        );
    }

    #[test]
    fn with_game_result() {
        let ptn = r#"[Player1 "a"][Player2 "b"] 1. a3 a2 2. a3- b2 d4 {hi} 0-1"#;
        let moves = vec!["a3", "a2", "a3-", "b2", "d4"];
        let mut comment_groups: Vec<Vec<String>> = (0..moves.len()).map(|_| Vec::new()).collect();
        comment_groups.push(vec!["hi".into()]);
        assert_eq!(
            ptn.parse::<Ptn>().unwrap(),
            Ptn::new(
                vec![Tag::new("Player1", "a"), Tag::new("Player2", "b"),],
                moves
                    .into_iter()
                    .map(|m| m.parse::<Move>())
                    .collect::<Result<_, _>>()
                    .unwrap(),
                comment_groups,
                Some(GameResult::Black(WinReason::Other)),
            )
        );
    }

    #[test]
    fn no_tags_game_result_and_whitespace() {
        let ptn = r#"a3 a2 a3- b2 d4 {hi} R-0         "#;
        let moves = vec!["a3", "a2", "a3-", "b2", "d4"];
        let mut comment_groups: Vec<Vec<String>> = (0..moves.len()).map(|_| Vec::new()).collect();
        comment_groups.push(vec!["hi".into()]);
        assert_eq!(
            ptn.parse::<Ptn>().unwrap(),
            Ptn::new(
                vec![],
                moves
                    .into_iter()
                    .map(|m| m.parse::<Move>())
                    .collect::<Result<_, _>>()
                    .unwrap(),
                comment_groups,
                Some(GameResult::White(WinReason::Road)),
            )
        );
    }

    #[test]
    fn starting_as_black() {
        let ptn = r#"[TPS "2,x5/x6/x2,2,x3/x3,1,1,x/x6/x5,1 2 3"] -- Cd4 d2 e4 c2"#;
        let moves = vec!["Cd4", "d2", "e4", "c2"];
        let comment_groups: Vec<Vec<String>> = (0..moves.len() + 1).map(|_| Vec::new()).collect();
        assert_eq!(
            ptn.parse::<Ptn>().unwrap(),
            Ptn::new(
                vec![Tag::new("TPS", "2,x5/x6/x2,2,x3/x3,1,1,x/x6/x5,1 2 3")],
                moves
                    .into_iter()
                    .map(|m| m.parse::<Move>())
                    .collect::<Result<_, _>>()
                    .unwrap(),
                comment_groups,
                None,
            )
        );
    }

    #[test]
    fn transform_ptn_file() {
        transform::<Ptn, _, _>([(
            r#"[Player1 "a"][Player2 "b"] {hello}  {there} 1. a3 a2 2. a3- b2 d4 {hi} 0-1"#,
            "[Player1 \"a\"]\n[Player2 \"b\"]\n\n{hello} {there}\n1. a3 a2\n2. a3- b2\n3. d4 {hi} 0-1\n",
        ),
        (
            r#"[a    "a"]   [b  "b"  ] 1. a3{"what"}{is}  {this}a2 a3- b2 d4 {cool}   "#,
            "[a \"a\"]\n[b \"b\"]\n\n1. a3 {\"what\"} {is} {this} a2\n2. a3- b2\n3. d4 {cool}\n",
        )]);
    }

    #[test]
    fn common_tags() {
        let ptn_string = r#"
[Caps "1"]
[Flats "2"]
[Clock "15:0 +15"]
[Date "2022.10.27"]
[Event "hi"]
[Komi "2"]
[Opening "swap"]
[Player1 "a"]
[Player2 "b"]
[Rating1 "123"]
[Rating2 "1233"]
[Round "1"]
[Site "ptn.ninja"]
[Size "6"]
[Time "07:49:59"]
[TPS "x6/1,x2,2,x2/x,2,1,1,x2/x,2,x4/x,1,x,1,x2/x6 2 32"]
        "#;
        let ptn: Ptn = ptn_string.parse().unwrap();
        assert_eq!(ptn.caps(), Some(1));
        assert_eq!(ptn.flats(), Some(2));
        assert_eq!(ptn.clock(), Some("15:0 +15"));
        assert_eq!(ptn.date(), Some(NaiveDate::from_ymd(2022, 10, 27)));
        assert_eq!(ptn.event(), Some("hi"));
        assert_eq!(ptn.komi(), Some(2));
        assert_eq!(ptn.half_komi(), Some(4));
        assert_eq!(ptn.opening(), Some("swap"));
        assert_eq!(ptn.player_1(), Some("a"));
        assert_eq!(ptn.player_2(), Some("b"));
        assert_eq!(ptn.rating_1(), Some(123));
        assert_eq!(ptn.rating_2(), Some(1233));
        assert_eq!(ptn.site(), Some("ptn.ninja"));
        assert_eq!(ptn.size(), Some(6));
        assert_eq!(ptn.time(), Some(NaiveTime::from_hms(7, 49, 59)));
        assert_eq!(
            ptn.tps(),
            Tps::from_str("x6/1,x2,2,x2/x,2,1,1,x2/x,2,x4/x,1,x,1,x2/x6 2 32").ok()
        );
    }
}
