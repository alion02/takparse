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
}
