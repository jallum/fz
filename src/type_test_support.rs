use crate::types_seam::Ty;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtomTypeTest {
    None,
    Any,
    Finite(Vec<String>),
    Cofinite,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeTestShape {
    pub ints: bool,
    pub atoms: AtomTypeTest,
    pub floats: bool,
    pub basic: crate::types::BasicBits,
    pub tuple_has_negations: bool,
    pub tuple_arities: Vec<usize>,
}

pub(crate) fn shape(a: &Ty) -> TypeTestShape {
    let mut ints = false;
    let mut atoms = AtomTypeTest::None;
    let mut floats = false;
    let mut basic = crate::types::BasicBits::NONE;
    let mut tuple_has_negations = false;
    let mut tuple_arities = Vec::new();
    for component in a.descr().components() {
        match component {
            crate::types::Component::Ints(_) => ints = true,
            crate::types::Component::Atoms(view) => {
                atoms = if view.is_any() {
                    AtomTypeTest::Any
                } else if view.cofinite() {
                    AtomTypeTest::Cofinite
                } else {
                    AtomTypeTest::Finite(
                        view.finite()
                            .expect("finite (non-cofinite)")
                            .map(String::from)
                            .collect(),
                    )
                };
            }
            crate::types::Component::Floats(_) => floats = true,
            crate::types::Component::Basic(bits) => basic = bits,
            crate::types::Component::Tuples(view) => {
                tuple_has_negations = view.has_negations();
                tuple_arities.extend(view.arities());
            }
            crate::types::Component::Opaques(_)
            | crate::types::Component::Brands(_)
            | crate::types::Component::Vars(_)
            | crate::types::Component::Lists(_)
            | crate::types::Component::Funcs(_)
            | crate::types::Component::Maps(_) => {}
        }
    }
    tuple_arities.sort_unstable();
    tuple_arities.dedup();
    TypeTestShape {
        ints,
        atoms,
        floats,
        basic,
        tuple_has_negations,
        tuple_arities,
    }
}
