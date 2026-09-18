# SCOPE — what is / is not proved for the prize (JSP-000415)

## Headline target

- Required theorem: `monochromatic_path_cover` (see ACCEPTANCE.md / acceptance.json)
- **Status: WIP.** Definitions, lemma skeleton and harness exist; the full
  inductive proof of PVW24 Theorem 1.3 is being formalized.

## What the headline must cover

| Component | Source | Lean target |
|---|---|---|
| two monochromatic paths cover 2-coloured $K_n$ | GeGy67 / Thm 1.1 | `gerencser_gyarfas` |
| bipartite Ramsey for paths | GyLe73 / Lem 2.1 | `bip_ramsey_path` |
| degree ⇒ one covering path | Lem 2.2 | `path_cover_of_min_degree` |
| degree ⇒ few covering paths | Lem 2.3 | `few_paths_of_min_degree` |
| refined cover lemma | Lem 2.4 | `refined_path_cover` |
| overlap lemma | Lem 3.1 | `overlap_bound` |
| long-path structure lemma | Lem 3.2 | `long_path_structure` |
| tail-pairing bound | Lem 3.3 | `tail_pairing_bound` |
| weak bound $f(n)<\sqrt n+20^4$ | Prop 3.4 | `weak_sqrt_bound` |
| **headline** $f(n)\le\sqrt n$, $n>20^{40}$ | Thm 1.3 | `monochromatic_path_cover` |

## Deliberate modeling choices

- Vertex set `Fin n`; a 2-colouring of $K_n$ is a `SimpleGraph (Fin n)` (red
  graph); blue edges are non-adjacent distinct pairs. Paths are `List`-based
  vertex paths (`Nodup` + `Chain'` adjacency) rather than `SimpleGraph.Path`,
  because the proof constantly reorders/splices vertex sequences
  ($v_1\ldots v_i v_j v_{j-1}\ldots v_{i+1} y\, v_{j+1}\ldots v_r$).
- Bound `card ≤ √n` is stated as a real inequality `(card : ℝ) ≤ Real.sqrt n`,
  equivalent to `card ≤ Nat.sqrt n`; the paper's literal "$\sqrt n$ paths".
- `f(n,χ)`/`f(n)` are not needed as functions; lemmas are stated directly as
  existence/non-existence of small same-colour covers under strong induction.

## Out of scope (paper remarks, not required by catalog)

- The conjecture for small $n$ ($n \le 20^{40}$); the paper does not settle it.
- The stronger $\sqrt n + 10$ bound for all $n$ mentioned in the remark.
- Vertex-**disjoint** covers (false here, per the paper's remark after Thm 1.2).
- The Gyárfás $r$-colour conjecture ($r$ disjoint monochromatic paths) — open.

## Prize rules reminder

Only a COMPLETE formalization of the ORIGINAL catalog problem is eligible.
No award claim issue is to be opened until every ACCEPTANCE item is green;
nothing is to be PR'd to TheJustinSunPrize/awards.
