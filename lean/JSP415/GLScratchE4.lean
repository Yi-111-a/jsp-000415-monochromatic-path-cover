import JSP415.GLScratchE4a
import JSP415.GLScratchE4b
import JSP415.GLScratchE4c

/-!
# GLScratchE4 — Claim E, forward direction (`j ≥ i + 5`)

`Case3Data.e_dir`: for `u = A[i]` (`i` even, `Y`-side) and `l = A[j]`
(`j` odd, `X`-side) with `i + 5 ≤ j`, the edge `A[i]–A[j]` is red.
Dispatches to `e_dir_main` (`i ≥ 2`), `e_dir_i0` (`i = 0`, `j + 2 < r`),
and `e_dir_i0r2` (`i = 0`, `j + 2 = r`).
-/

open Finset
open Classical

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

namespace Case3Data

theorem e_dir (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hB' : c3.ClaimB') (hC : ∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u)
    (hux2 : c3.HasUx2) {i j : ℕ}
    (hi : i < c3.A.length) (hpar : i % 2 = 0)
    (hj : j < c3.A.length) (hjp : j % 2 = 1) (hij : i + 5 ≤ j) :
    G.Adj c3.A[i] c3.A[j] := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · -- `i = 0`: `j + 2 ≤ r` since `j < r`, `j` odd, `r` odd
    have hro : c3.A.length % 2 = 1 := c3.r_odd hXY
    rcases lt_or_ge (j + 2) c3.A.length with hjr | hjr
    · exact c3.e_dir_i0 hXY hB' hC hux2 hj hjp (by omega) hjr
    · exact c3.e_dir_i0r2 hXY hB' hC hux2 hj hjp (by omega) (by omega)
  · exact c3.e_dir_main hXY hB' hC hux2 hi hpar hj hjp hij (by omega)

end Case3Data

end JSP415
