# JSP-000415 — Can every edge-colored complete graph have its vertices covered by few paths whose edges all share one color?

- **id:** JSP-000415
- **title:** Can every edge-colored complete graph have its vertices covered by few paths whose edges all share one color?
- **area:** Graph theory / Ramsey theory
- **status:** Solved
- **Lean:** No (formalization target)
- **Eligible / Claim:** No / Unavailable
- **role:** Formalize path (Solved + Lean=No)

## Statement

Can every edge-colored complete graph have its vertices covered by few paths whose edges all share one color?

More precisely (Erdős–Gyárfás): in a 2-edge-colouring of \(K_n\), how small a monochromatic *same-colour* path cover can one guarantee?

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000415
- Awards home: https://github.com/TheJustinSunPrize/awards

## Primary papers

- [PVW24] A proof of a conjecture of Erdős and Gyárfás on monochromatic path covers — arXiv:2409.03623 (2024). **Main formalization source.**
- [ErGy95] Vertex covering with monochromatic paths — Math. Pannon. (1995).
- [GeGy67] On Ramsey-type problems — Ann. Univ. Sci. Budapest. Eötvös Sect. Math. (1967).

## Accepted mathematical answer

For all sufficiently large \(n\), every 2-edge-colouring of \(K_n\) admits a cover of \(V(K_n)\) by at most \(\sqrt{n}\) monochromatic paths **all of the same colour** (PVW24 Theorem 1.3). Paths of length 0 are allowed.

## Success criteria

- `lake build` succeeds
- Zero `sorry` / `admit`
- Named headline theorem(s) in ACCEPTANCE.md proved
