# Lean 4 formal verification

[`Wowii138.lean`](Wowii138.lean) is a Lean 4 formalization of **one** of the
18-vertex counterexamples: the tree `T18` whose edge list is
[`../data/tree-18-original-labels.edges`](../data/tree-18-original-labels.edges)
(isomorphic to `A18`). The main theorem is

```lean
theorem connected_counterexample : T18.Connected ∧ ¬ Conjecture138 T18
```

## What is formalized

* The WOWII notions used by conjecture #138: the square graph `G²`, the
  maximum-degree vertex set `M(G)`, `dist_min(M(G²))` (distances measured in
  `G²`), the unique-maximum-independent-set indicator `u(G)` (definition 74
  read through its title; see the main README), induced paths (both an
  inductive and a textbook definition, proved equivalent), and the conjecture
  itself: `Conjecture138 G` is "G has an induced path with at least
  `(2 + u(G)) * dist_min(M(G²))` vertices".
* The graph `T18`: its 17 edges, that it is connected and acyclic (a tree),
  and that every adjacency it declares is in the published edge list and vice
  versa.
* `u(T18) = 1`: the unique maximum independent set is
  `S0 = {1,2,3,4,6,8,10,12,15,16,17}` (size 11).
* `M(T18²) = {1, 13}`, `dist_{T18²}(1,13) = 5`, hence
  `dist_min(M(T18²)) = 5`.
* Every induced path of `T18` has at most 14 vertices, and a 14-vertex induced
  path exists (so `path(T18) = 14`).
* Therefore `14 < (2 + 1) * 5 = 15`, so conjecture #138 fails for `T18`.

## Kernel check

The file contains no `sorry`, no `admit`, no axioms of its own, and no
`native_decide`. It ends with three `#print axioms` commands; the output is
exactly

```
'Wowii138.conjecture138_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wowii138.connected_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wowii138.T18_path_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
```

so the formal proof rests only on Lean's standard axioms.

## What is NOT formalized

* **Only one witness.** The statement that there are exactly three
  18-vertex counterexamples up to isomorphism is not formalized here.
* **No minimality.** The exhaustive search over all unlabeled trees with
  `3 <= n <= 18` (205,002 trees) is done by
  [`../search/search_trees.py`](../search/search_trees.py) with nauty; that
  computation is not verified in Lean.
* The 21-vertex witness `T21` and the family behind it are not formalized.
* The Lean statement uses the intended reading of the published statement
  (unique *maximum* independent set, distances measured in `G²`), the same
  reading as [`../verify.py`](../verify.py).

## Reproducing

Checked with Lean `4.37.0-rc1` (toolchain `leanprover/lean4:v4.37.0-rc1`)
and Mathlib commit `c44d09c9afd6296ba2d4c0c3712b3592ac899078`.

```bash
# 1. Mathlib at the pinned commit, with its build cache
git clone https://github.com/leanprover-community/mathlib4
cd mathlib4
git checkout c44d09c9afd6296ba2d4c0c3712b3592ac899078
lake exe cache get

# 2. check the file (about 70-100 s on 4 cores; it disables the heartbeat limit)
lake env lean /path/to/wowii-conjecture-138/lean/Wowii138.lean
```

Exit status 0 and no diagnostics besides the three `#print axioms` lines mean
the file was checked successfully.

The Lean source is covered by the repository's MIT license (see
[`../LICENSE`](../LICENSE)); the surrounding text is CC BY 4.0 (see
[`../LICENSE-CONTENT.md`](../LICENSE-CONTENT.md)).
