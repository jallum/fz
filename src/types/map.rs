/// Open-shape map keys are concrete singleton values.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub enum MapKey {
    Atom(String),
    Int(i64),
}
