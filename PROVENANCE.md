# Provenance and AI disclosure

[Back to the README](README.md)

This repository is published as a **public record of a personal AI-assisted
exploration**. It makes **no priority claim**: current models are strong enough
that similar counterexamples may well have been found independently, and no
systematic literature search was attempted. The only check made was that
*Written on the Wall II* still listed conjecture #138 as open on 2026-11-25.

## How the witnesses were produced (UTC, 2026-11-25)

| time | event | evidence |
| --- | --- | --- |
| 13:06:14 | Codex session `01a212d0-4743-7213-8b9e-22a59d508eac` starts in `C:\Users\PC\Documents\Codex\2026-11-25\jie`, model `gpt-6.2-astra` | Codex rollout `~/.codex/sessions/2026/11/25/rollout-2026-11-25T21-06-14-01a212d0-…jsonl` (retained on the author's machine; sha256 `fa328163…81830`) |
| 13:12:32 | GPT 6.2 Astra reports the construction: a 21-vertex tree with `path = 17`, `u = 1`, `M(G²) = {0,12}` and `dist_min = 6`, so the conjecture requires `17 ≥ 18` | session transcript |
| 13:13:10 | writes an exact verifier `outputs/verify_wowii_138.py`, which recomputes everything from the edge list and asserts the tuple `(17, 18, 1, 6, [0,12], 6, 12)`; the run at 13:13:27 passes | script sha256 `f84c8a38…d3059f` (kept with the session record) |
| 14:33 | three 18-vertex counterexamples found by exhaustive search over all unlabeled trees with 3 ≤ n ≤ 18 (nauty `geng`); no smaller tree violates the conjecture | [`search/results.txt`](search/results.txt), [`data/`](data/) |
| 14:40:43 | GitHub repository `yutitan/wowii-conjecture-138` created, public | GitHub API `created_at` |
| 14:48:00 | first commit `d7f849e` pushed to `main` | GitHub API `commits/main` |
| 14:48:27 | release `v1.0.0` published | GitHub API `releases` |

The GitHub timestamps are server-side and can be checked directly:

```bash
curl -s https://api.github.com/repos/yutitan/wowii-conjecture-138 | grep created_at
curl -s https://api.github.com/repos/yutitan/wowii-conjecture-138/commits/main | grep -m2 date
curl -s https://api.github.com/repos/yutitan/wowii-conjecture-138/releases | grep published_at
```

## Consistency of the published witness

* The 20 edges of [`data/tree-21.edges`](data/tree-21.edges) are exactly the
  edge list hard-coded in the verifier written at 13:13 UTC (sha256 of
  `data/tree-21.edges`: `8ff0be6d…f0835e`), so the published `T21` is the same
  tree that was derived in that session, not a later reconstruction.
* The tree of the first public commit has hash
  `43e936ff71f23393cbdae2d9d2e20cca3dfeb493` (the local initial commit
  `a3c51d4`, created before the upload, has the same tree).
* All numerical claims are re-derived from the edge lists by
  [`verify.py`](verify.py); running `python3 verify.py` reproduces
  [`verify.out`](verify.out) without any third-party software.

## What the AI systems did

* **GPT 6.2 Astra** (OpenAI Codex, model `gpt-6.2-astra`) derived the 21-vertex
  witness `T21` and wrote its first exact verifier.
* **DeepSeek Harness** (an AI coding agent) carried out, under the same human
  direction, the exhaustive search over all trees with 3–18 vertices that
  produced the three 18-vertex counterexamples and the minimality result, and
  assembled and published this repository.
* The **human author** ([@yutitan](https://github.com/yutitan)) initiated and
  directed both sessions, reviewed the output, published the repository, and
  takes responsibility for its content. AI systems are not legal authors.

## Lean 4 formalization (2026-11-26)

The 18-vertex witness `T18`
([`data/tree-18-original-labels.edges`](data/tree-18-original-labels.edges),
isomorphic to `A18`) was formalized in Lean 4 on 2026-11-26 with an AI coding
agent (WorkBuddy session) under the same human direction. The file
[`lean/Wowii138.lean`](lean/Wowii138.lean) was then independently compiled and
axiom-audited: Lean 4.37.0-rc1 with Mathlib
`c44d09c9afd6296ba2d4c0c3712b3592ac899078`, exit status 0, no `sorry`, no
`native_decide`, and `#print axioms` reports only `propext`,
`Classical.choice`, `Quot.sound`. Only one witness is formalized; the
three-witness count and the exhaustive minimality search remain Python-only.
See [`lean/README.md`](lean/README.md).

## A note on the statement

Two defects of the published statement are discussed in the README: definition
74 omits the word "maximum", and `dist_min(M(G²))` can be measured in `G²` or
in `G`. The counterexamples violate the inequality in both readings, so the
claims do not depend on either interpretation.
