# ACCEPTANCE — JSP-000415 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000415
- Awards CONTRIBUTING: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md

## Exact original question (English)

> Can every edge-colored complete graph have its vertices covered by few paths whose edges all share one color?

The accepted resolution is PVW24 Theorem 1.3 (arXiv:2409.03623): there exists \(n_0\) such that for all \(n>n_0\), every 2-edge-colouring of \(K_n\) has a vertex cover by at most \(\sqrt{n}\) monochromatic paths **all of the same colour**.

The older Erdős–Gyárfás \(2\sqrt{n}\) bound alone is **not** the full catalog answer.

## Required Lean theorem name(s) (FULL statement)

| Lean name | Intended statement |
|---|---|
| `monochromatic_path_cover` | For all \(n > 20^{40}\) (paper threshold) and every 2-edge-colouring of \(K_n\), there is a same-colour monochromatic path cover of size \(\le \sqrt{n}\). |

**Not sufficient for prize_ready:** the weak \(2\sqrt{n}\) theorem, mixed-colour covers (Gerencsér–Gyárfás), or intermediate bipartite lemmas alone.

## Checklist (all must pass)

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit` in all `*.lean` (excluding `.lake`)
- [ ] `#print axioms` on headline theorem(s) shows only standard axioms
- [ ] Public repo HEAD is a full 40-character commit SHA
- [ ] README documents build instructions
- [ ] `formalization.yaml` and/or `ATTRIBUTION.md` name `Yi-111-a` / operators
- [ ] Named headline theorem(s) above exist and are proved

## Harness rule

`prize_ready=true` **only** when every checklist item passes **and** the named headline theorem(s) exist and are proved.
