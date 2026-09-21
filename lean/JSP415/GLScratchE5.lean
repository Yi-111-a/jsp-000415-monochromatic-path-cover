import JSP415.GLScratchE4
import JSP415.GLScratchE5a

/-!
# GLScratchE5 — Claim E, reverse direction (`i ≥ j + 5`)

`Case3Data.e_rev`: for `u = A[i]` (`i` even, `Y`-side) and `l = A[j]`
(`j` odd, `X`-side) with `j + 5 ≤ i`, the edge `A[i]–A[j]` is red.
This is `e_dir` transported through the `A`-reversed case-3 data
(`GLScratchE5a.revCase3`): `A.reverse[r-1-i] = A[i]` and `r` odd
preserve the side parities.
-/

open Finset
open Classical

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

namespace Case3Data

theorem e_rev (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hB' : c3.ClaimB') (hC : ∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u)
    (hux2 : c3.HasUx2) {i j : ℕ}
    (hi : i < c3.A.length) (hpar : i % 2 = 0)
    (hj : j < c3.A.length) (hjp : j % 2 = 1) (hij : j + 5 ≤ i) :
    G.Adj c3.A[i] c3.A[j] :=
  e_rev_core (fun c' hXY' hB'' hC' hux2' ↦ c'.e_dir hXY' hB'' hC' hux2')
    c3 hXY hB' hC hux2 hi hpar hj hjp hij

end Case3Data

end JSP415
