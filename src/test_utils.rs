use std::{
    fmt::{Debug, Display},
    str::FromStr,
};

pub fn round_trip<'a, T: FromStr<Err = E> + Display, E: Debug, I: IntoIterator<Item = &'a str>>(
    cases: I,
) {
    transform::<T, _, _>(cases.into_iter().map(|s| (s, s)));
}

pub fn transform<
    'a,
    T: FromStr<Err = E> + Display,
    E: Debug,
    I: IntoIterator<Item = (&'a str, &'a str)>,
>(
    from_to_pairs: I,
) {
    from_to_pairs
        .into_iter()
        .for_each(|(from, to)| assert_eq!(from.parse::<T>().unwrap().to_string(), to));
}

pub fn error<'a, T: FromStr<Err = E> + Debug, E: Debug + Eq, I: IntoIterator<Item = &'a str>>(
    cases: I,
    err: E,
) {
    cases
        .into_iter()
        .for_each(|s| assert_eq!(s.parse::<T>().unwrap_err(), err));
}
