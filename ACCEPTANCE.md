# ACCEPTANCE — JSP-000415 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000415
- Awards CONTRIBUTING: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md

## Exact original question (English)

> Can every edge-colored complete graph have its vertices covered by few paths
> whose edges all share one color?

The accepted resolution is Theorem 1.3 of arXiv:2409.03623v2: for all
$n > 20^{40}$, every 2-edge-coloured $K_n$ admits a vertex cover by at most
$\sqrt n$ monochromatic paths **all of the same colour** (length-0 paths
allowed, paths may intersect, $\lfloor\sqrt n\rfloor$ interpretation).

## Required Lean theorem name(s) (FULL statement)

| Lean name | Intended statement |
|---|---|
| `monochromatic_path_cover` | For every `n > 20^40` and every `G : SimpleGraph (Fin n)` (read: `Adj` = red, `¬Adj` = blue on distinct vertices), there exists a `Finset` of vertex paths, all monochromatic in one fixed colour, covering every vertex, with `card ≤ √n` (real comparison). |

**Not sufficient for prize_ready:** Thm 1.1 alone, Lemma 2.x/3.x fragments,
`f n < √n + C` for `C > 0`, the small-`n` regime `n ≤ 20^40`, or any version
allowing the cover to mix colours.

## Checklist (all must pass)

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit` in all `*.lean` (excluding `.lake`)
- [ ] `#print axioms monochromatic_path_cover` shows only `[propext, Classical.choice, Quot.sound]`
- [ ] Public repo HEAD is a full 40-character commit SHA
- [ ] README documents build instructions
- [ ] `formalization.yaml` and/or `ATTRIBUTION.md` name `Yi-111-a` / operators
- [ ] Named headline theorem(s) above exist and are proved

## Harness rule

`prize_ready=true` **only** when every checklist item passes **and** the named
headline theorem(s) exist and are proved. Harness-green intermediate lemmas do
not count as success.
