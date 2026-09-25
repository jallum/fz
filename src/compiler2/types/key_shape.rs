//! Read-only projection of value variables into the existing call-key algebra.

use super::*;
use crate::compiler2::return_unknowns::KeyShape;

impl Types {
    /// Locate variables owned by the enclosing value coordinate. Callable
    /// signatures have their own binders and remain ordinary concrete values.
    /// This reads descriptors directly so membership and key admission can
    /// bind the same source shape without interning types during discovery.
    pub(crate) fn input_key_shape(&self, input: Ty) -> KeyShape {
        input_key_shape(self.ctx(), self.descr(&input), &mut HashSet::new())
    }
}

fn input_key_shape(cx: TyCtx<'_>, input: &Descr, active: &mut HashSet<Descr>) -> KeyShape {
    if !has_vars(cx, input) {
        return KeyShape::Settled;
    }
    if pure_var_ids(input).is_some() || !active.insert(input.clone()) {
        return KeyShape::Unknown;
    }
    let shape = if let Some(arity) = exclusive_tuple_root_arity(input) {
        let fields = tuple_projections(cx, input, arity)
            .iter()
            .map(|field| input_key_shape(cx, field, active))
            .collect::<Vec<_>>();
        if fields.iter().all(KeyShape::is_settled) {
            KeyShape::Settled
        } else {
            KeyShape::Tuple(fields)
        }
    } else if input.cases.iter().any(|case| !case.structure.lists.is_empty()) {
        let element = list_element_type(cx, input);
        let shape = input_key_shape(cx, &element, active);
        if shape.is_settled() {
            KeyShape::Settled
        } else {
            KeyShape::List(Box::new(shape))
        }
    } else {
        let fields = map_known_keys(input)
            .into_iter()
            .filter_map(|key| {
                let field = map_field_lookup(cx, input, &key)?;
                Some((key, input_key_shape(cx, &field, active)))
            })
            .collect::<Vec<_>>();
        if fields.iter().all(|(_, shape)| shape.is_settled()) {
            KeyShape::Settled
        } else {
            KeyShape::Map(fields)
        }
    };
    active.remove(input);
    shape
}
