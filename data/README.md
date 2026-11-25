# Data files

Every tree is stored twice:

* `<name>.edges` — one edge per line as `u v`, vertices `0 .. n-1`;
  lines starting with `#` are comments;
* `<name>.g6` — the same graph in
  [graph6](https://users.cecs.anu.edu.au/~bdm/data/formats.html) format.

| file | n | description |
| --- | --- | --- |
| `tree-A18` | 18 | smallest counterexample, nauty canonical labelling |
| `tree-B18` | 18 | smallest counterexample, nauty canonical labelling |
| `tree-C18` | 18 | smallest counterexample, nauty canonical labelling |
| `tree-21` | 21 | the 21-vertex witness, in its original labelling |
| `tree-18-original-labels` | 18 | an 18-vertex witness isomorphic to `tree-A18`, in its original labelling (kept for provenance) |

`A18`, `B18` and `C18` are, up to isomorphism, exactly the trees on 18
vertices that violate conjecture #138; see `search/results.txt`.

Run `python3 verify.py` from the repository root to check all witnesses.
