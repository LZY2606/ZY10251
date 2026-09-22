use std::collections::{HashMap, HashSet};

use crate::rust_types::{
    RustConst, RustEnum, RustEnumVariant, RustItem, RustStruct, RustType, RustTypeAlias,
    SpecialRustType,
};

/// Traversal state for the legacy topological dependency walk.
///
/// This walk intentionally preserves the quirks of the original implementation
/// (e.g. dependencies are keyed by the item's *original* name even after
/// `serde(rename)` reconciliation, anonymous struct variants never contribute
/// dependencies, and generic parameters of a generic item are visited after the
/// item itself). Both the legacy in-place [`topsort`] and the canonical graph
/// freeze use it so that generated ordering stays byte identical.
pub(crate) struct DependencyWalker<'a> {
    types: &'a HashMap<String, &'a RustItem>,
}

impl<'a> DependencyWalker<'a> {
    /// Build a name lookup table from a slice of items.
    pub(crate) fn index(items: impl Iterator<Item = &'a RustItem>) -> HashMap<String, &'a RustItem> {
        HashMap::from_iter(items.map(|thing| (item_original_name(thing).to_string(), thing)))
    }

    /// Create a walker over the given lookup table.
    pub(crate) fn new(types: &'a HashMap<String, &'a RustItem>) -> Self {
        Self { types }
    }

    /// Collect the transitive dependencies of `thing` in first-visit order.
    pub(crate) fn dependencies(&self, thing: &RustItem) -> Vec<String> {
        let mut res = Vec::new();
        let mut seen = HashSet::new();
        self.get_dependencies(thing, &mut res, &mut seen);
        res
    }

    fn get_dependencies_from_type(
        &self,
        tp: &RustType,
        res: &mut Vec<String>,
        seen: &mut HashSet<String>,
    ) {
        match tp {
            RustType::Generic { id, parameters } => {
                if let Some(tp) = self.types.get(id) {
                    if seen.insert(id.clone()) {
                        res.push(id.clone());
                        self.get_dependencies(tp, res, seen);
                        for parameter in parameters {
                            let id = parameter.id().to_string();
                            if let Some(tp) = self.types.get(&id) {
                                if seen.insert(id.clone()) {
                                    res.push(id.clone());
                                    self.get_dependencies(tp, res, seen);
                                    seen.remove(&id.clone());
                                }
                            }
                        }
                        seen.remove(&id.clone());
                    }
                }
            }
            RustType::Simple { id } => {
                if let Some(tp) = self.types.get(id) {
                    if seen.insert(id.clone()) {
                        res.push(id.clone());
                        self.get_dependencies(tp, res, seen);
                        seen.remove(&id.clone());
                    }
                }
            }
            RustType::Special(special) => match special {
                SpecialRustType::HashMap(kt, vt) => {
                    self.get_dependencies_from_type(kt, res, seen);
                    self.get_dependencies_from_type(vt, res, seen);
                }
                SpecialRustType::Option(inner) => {
                    self.get_dependencies_from_type(inner, res, seen);
                }
                SpecialRustType::Vec(inner) => {
                    self.get_dependencies_from_type(inner, res, seen);
                }
                _ => {}
            },
        };
        seen.remove(&tp.id().to_string());
    }

    fn get_enum_dependencies(
        &self,
        enm: &RustEnum,
        res: &mut Vec<String>,
        seen: &mut HashSet<String>,
    ) {
        match enm {
            RustEnum::Unit(_) => {}
            RustEnum::Algebraic { shared, .. } => {
                if seen.insert(shared.id.original.to_string()) {
                    res.push(shared.id.original.to_string());
                    for variant in &shared.variants {
                        if let RustEnumVariant::Tuple { ty, .. } = variant {
                            self.get_dependencies_from_type(ty, res, seen)
                        }
                    }
                    seen.remove(&shared.id.original.to_string());
                }
            }
        }
    }

    fn get_struct_dependencies(
        &self,
        strct: &RustStruct,
        res: &mut Vec<String>,
        seen: &mut HashSet<String>,
    ) {
        if seen.insert(strct.id.original.to_string()) {
            for field in &strct.fields {
                self.get_dependencies_from_type(&field.ty, res, seen)
            }
            seen.remove(&strct.id.original.to_string());
        }
    }

    fn get_type_alias_dependencies(
        &self,
        ta: &RustTypeAlias,
        res: &mut Vec<String>,
        seen: &mut HashSet<String>,
    ) {
        if seen.insert(ta.id.original.to_string()) {
            self.get_dependencies_from_type(&ta.r#type, res, seen);
            for generic in &ta.generic_types {
                if let Some(thing) = self.types.get(generic) {
                    self.get_dependencies(thing, res, seen)
                }
            }
            seen.remove(&ta.id.original.to_string());
        }
    }

    fn get_const_dependencies(
        &self,
        c: &RustConst,
        res: &mut Vec<String>,
        seen: &mut HashSet<String>,
    ) {
        if seen.insert(c.id.original.to_string()) {
            self.get_dependencies_from_type(&c.r#type, res, seen);
            seen.remove(&c.id.original.to_string());
        }
    }

    fn get_dependencies(
        &self,
        thing: &RustItem,
        res: &mut Vec<String>,
        seen: &mut HashSet<String>,
    ) {
        match thing {
            RustItem::Enum(en) => self.get_enum_dependencies(en, res, seen),
            RustItem::Struct(strct) => self.get_struct_dependencies(strct, res, seen),
            RustItem::Alias(alias) => self.get_type_alias_dependencies(alias, res, seen),
            RustItem::Const(c) => self.get_const_dependencies(c, res, seen),
        }
    }
}

/// The original (pre-rename) name used as the legacy dependency key.
pub(crate) fn item_original_name(thing: &RustItem) -> &str {
    match thing {
        RustItem::Enum(e) => &e.shared().id.original,
        RustItem::Struct(strct) => &strct.id.original,
        RustItem::Alias(ta) => &ta.id.original,
        RustItem::Const(c) => &c.id.original,
    }
}

fn get_index(thing: &RustItem, things: &[RustItem]) -> usize {
    things
        .iter()
        .position(|r| r == thing)
        .expect("Unable to find thing in things!")
}

#[allow(clippy::ptr_arg)] // Ignored due to false positive
fn toposort_impl(graph: &Vec<Vec<usize>>) -> Vec<usize> {
    fn inner(
        graph: &Vec<Vec<usize>>,
        nodes: &Vec<usize>,
        res: &mut Vec<usize>,
        processed: &mut Vec<usize>,
        seen: &mut Vec<usize>,
    ) {
        for dependant in nodes {
            if !processed.contains(dependant) {
                if !seen.contains(dependant) {
                    seen.push(*dependant);
                } else {
                    // cycle
                    return;
                }
                // recurse
                let dependencies = &graph[*dependant];
                inner(graph, dependencies, res, processed, seen);
                if let Some(position) = seen.iter().position(|&other| other == *dependant) {
                    seen.remove(position);
                }
                processed.push(*dependant);
                res.push(*dependant);
            }
        }
    }
    let mut res = vec![];
    let mut seen = vec![];
    let mut processed = vec![];
    inner(
        graph,
        &(0..graph.len()).collect(),
        &mut res,
        &mut processed,
        &mut seen,
    );
    res
}

pub(crate) fn topsort(things: &mut [RustItem]) {
    let types = DependencyWalker::index(things.iter());
    let walker = DependencyWalker::new(&types);

    let dag: Vec<Vec<usize>> = things
        .iter()
        .map(|thing| {
            walker
                .dependencies(thing)
                .iter()
                .map(|dep| get_index(*types.get(dep).unwrap(), things))
                .collect()
        })
        .collect();
    sort_by_indices(things, toposort_impl(&dag));
}

/// In place sort of array using provided indices.
pub(crate) fn sort_by_indices<T>(data: &mut [T], mut indices: Vec<usize>) {
    for idx in 0..data.len() {
        if indices[idx] != idx {
            let mut current_idx = idx;
            loop {
                let target_idx = indices[current_idx];
                indices[current_idx] = current_idx;
                if indices[target_idx] == target_idx {
                    break;
                }
                data.swap(current_idx, target_idx);
                current_idx = target_idx;
            }
        }
    }
}

#[test]
fn test_toposort_impl() {
    let dag = vec![vec![], vec![0], vec![0, 1]];
    let res = toposort_impl(&dag);
    assert_eq!(res, vec![0, 1, 2])
}

#[test]
fn test_toposort_impl_cycles() {
    let dag = vec![vec![1], vec![0], vec![1]];
    let res = toposort_impl(&dag);
    assert!((res == vec![0, 1, 2]) || (res == vec![1, 0, 2]))
}
