use crate::{Move, ParseMoveError};
use std::{
    error::Error,
    fmt::{Display, Formatter, Result as FmtResult},
    iter::once,
    str::FromStr,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Tag {
    key: String,
    value: String,
}

impl Tag {
    pub fn new<A: Into<String>, B: Into<String>>(key: A, value: B) -> Self {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    pub fn key(&self) -> &'_ str {
        &self.key
    }

    pub fn value(&self) -> &'_ str {
        &self.value
    }
}

impl Display for Tag {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "[{} \"{}\"]", self.key, self.value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseTagError {
    NoOpeningBracket,
    MissingKey,
    NoOpeningQuotationMarks,
    IllegalEscape,
    MissingValue,
    NoClosingQuotationMarks,
    NoClosingBracket,
    GarbageAfterValue,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum WinReason {
    Road,
    Flat,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum GameResult {
    White(WinReason),
    Black(WinReason),
    #[default]
    Draw,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseGameResultError {
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Ptn {
    tags: Vec<Tag>,
    moves: Vec<Move>,
    comments: Vec<Vec<String>>,
    result: Option<GameResult>,
}

impl Ptn {
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
}

impl Display for Ptn {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        for tag in &self.tags {
            writeln!(f, "{tag}")?;
        }
        writeln!(f)?;
        let mut comment_groups = self.comments.iter();
        if let Some(game_comments) = comment_groups.next() {
            for comment in game_comments {
                write!(f, "{{{comment}}} ")?;
            }
            writeln!(f)?;
        }
        let mut moves = self.moves.iter();
        let mut turn = 1;
        while match (moves.next(), moves.next()) {
            (Some(white), Some(black)) => {
                let white_comments = comment_groups.next().unwrap().join("} {");
                let black_comments = comment_groups.next().unwrap().join("} {");
                writeln!(
                    f,
                    "{turn}. {white} {{{white_comments}}} {black} {{{black_comments}}}"
                )?;
                turn += 1;
                true
            }
            (Some(white), None) => {
                let white_comments = comment_groups.next().unwrap().join("} {");
                writeln!(f, "{turn}. {white} {{{white_comments}}}")?;
                false
            }
            _ => false,
        } {}
        if let Some(result) = self.result {
            writeln!(f, "{result}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParsePtnError {
    Tag(ParseTagError),
    Move(ParseMoveError),
    IncompleteMoveNum,
    UnclosedComment,
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
                (Outside, c) if !c.is_whitespace() => Move,
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

