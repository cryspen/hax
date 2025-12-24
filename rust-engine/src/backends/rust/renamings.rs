use std::{collections::HashMap, fmt::Debug, hash::Hash, sync::LazyLock};

use crate::backends::prelude::Rendered;

#[derive(Debug)]
struct Graph<K, T> {
    node: Option<T>,
    subtree: HashMap<K, Box<Graph<K, T>>>,
}

impl<K, T> Default for Graph<K, T> {
    fn default() -> Self {
        Self {
            node: Default::default(),
            subtree: Default::default(),
        }
    }
}

impl<K: 'static + Eq + Hash + Clone + Debug, T: Debug> Graph<K, T> {
    fn create_path(&mut self, path: &[K]) -> &mut Graph<K, T> {
        let mut current = self;
        for chunk in path {
            current = current.subtree.entry(chunk.clone()).or_default();
        }
        current
    }
    fn get_longest(&self, path: impl Iterator<Item = K>) -> Option<(Vec<K>, &T)> {
        let mut current = self;
        let mut subpath = vec![];
        let mut results = vec![];

        for chunk in path {
            if let Some(sub) = current.subtree.get(&chunk) {
                current = sub;
                subpath.push(chunk.clone());
                if let Some(node) = &current.node {
                    results.push((subpath.clone(), node));
                }
            } else {
                break;
            }
        }

        results.pop()
    }
    fn from_iter(it: impl Iterator<Item = (Vec<K>, T)>) -> Self {
        let mut root = Self::default();
        for (path, value) in it {
            root.create_path(&path).node = Some(value);
        }
        root
    }
}

static RENAMINGS: LazyLock<Graph<String, Vec<&'static str>>> = LazyLock::new(|| {
    let str = include_str!("renamings");

    Graph::from_iter(str.lines().map(|line| {
        let (l, r) = line.split_once(" ").unwrap();
        (
            l.split(":").map(|s| s.to_string()).collect(),
            r.split(":").collect(),
        )
    }))
});

/// Rename a `Rendered` name according, so that we refer to public names of core, not private names.
pub(super) fn rename_rendered(rendered: &mut Rendered) {
    let chunks = rendered
        .module
        .clone()
        .into_iter()
        .chain(rendered.path.clone());
    if let Some((chunks_slice, rename)) = RENAMINGS.get_longest(chunks) {
        let rename: Vec<String> = rename.iter().map(|s| s.to_string()).collect();
        if chunks_slice.len() >= rendered.module.len() {
            let remainings = chunks_slice.len() - rendered.module.len();
            let (mod_part, path_part) = rename.split_at((rename.len() - remainings).max(1));
            rendered.module = mod_part.to_vec();
            rendered.path.splice(0..remainings, path_part.to_vec());
        } else {
            rendered.module.splice(0..chunks_slice.len(), rename);
        }
    }
}
