use crate::{Move, ParseMoveError};
use std::{
    error::Error,
    fmt::{Display, Formatter, Result as FmtResult},
    iter::once,
    str::FromStr,
};
