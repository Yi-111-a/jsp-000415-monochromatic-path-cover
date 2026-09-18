import JSP415.Defs
import JSP415.Gerencser
import JSP415.BipLemmas
import JSP415.Section3

/-!
# JSP-000415 — Monochromatic path covers of 2-edge-coloured complete graphs

Formalization of the Erdős–Gyárfás conjecture (1995), resolved by
Pokrovskiy–Versteegen–Williams, *A proof of a conjecture of Erdős and Gyárfás
on monochromatic path covers*, arXiv:2409.03623.

## Headline theorem

`monochromatic_path_cover` — for all `n > 20^40`, every 2-edge-coloured
`K_n` (a `SimpleGraph (Fin n)`, with `Adj` read as *red* and non-adjacency of
distinct vertices as *blue*) admits a family of at most `√n` monochromatic
paths, **all of the same colour**, covering the whole vertex set.  Paths may
be single vertices (length 0) and may intersect; `√n` is a real bound, i.e.
`⌊√n⌋` paths.
-/
