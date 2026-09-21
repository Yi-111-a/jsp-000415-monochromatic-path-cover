import JSP415.GLScratchE4
import JSP415.GLScratchE5
import JSP415.GLScratchE6
import JSP415.GLScratchLC2

/-!
# GLScratchE7 — Claim E assembly

`Case3Data.claimE`: the red branch `S₁ = A ++ [z]` is internally red-complete.
Given `u = A[i]` (i even, `u ∈ S1U`) and `l ∈ SL` with `l ∈ A ∨ l = z`:
`l = z` is `e_z`; `l = A[j]` (j odd) splits on `|i - j|` —
`1` is a consecutive edge (`edgeA`), `3` is `claimD_even`/`claimD_odd`,
`≥ 5` is the rotation `e_dir`/`e_rev`.
-/

open Finset
open Classical

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

namespace Case3Data

/-- `G.Adj` form of a consecutive red edge. -/
theorem adjA (c3 : Case3Data G X Y) {i : ℕ} (hi : i + 1 < c3.A.length) :
    G.Adj c3.A[i] c3.A[i + 1] :=
  (edgeA c3 i hi).2

/-- Claim E (GL73): every `Y`-side vertex of `S₁` is `G`-adjacent to every
`X`-side vertex of `S` lying in `S₁` (in `A` or equal to `z`). -/
theorem claimE (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hux2 : c3.HasUx2) : c3.ClaimE := by
  intro u hu l hl hmem
  have hB' := claimB' hXY c3
  have hC := claimC hXY c3 hB'
  obtain ⟨huA, huY⟩ := (e3mem_S1U c3 hXY).mp hu
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp huA
  have hipar : i % 2 = 0 := (c3.a_side hXY i hi).1.mp huY
  rcases hmem with hlA | rfl
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hlA
    have hlX : c3.A[j] ∈ X := ((e3mem_SL c3).mp hl).2
    have hjpar : j % 2 = 1 := (c3.a_side hXY j hj).2.mp hlX
    rcases lt_trichotomy i j with hlt | heq | hgt
    · -- i < j: j - i odd, so j = i+1, i+3, or j ≥ i+5
      have hd : j = i + 1 ∨ j = i + 3 ∨ i + 5 ≤ j := by omega
      rcases hd with rfl | rfl | hdij
      · exact adjA c3 (by omega)
      · exact c3.claimD_even hXY hB' hC hux2 (by omega) hipar
      · exact c3.e_dir hXY hB' hC hux2 hi hipar hj hjpar hdij
    · subst heq; exact absurd hjpar (by omega)
    · -- j < i: i - j odd, so i = j+1, j+3, or i ≥ j+5
      have hd : i = j + 1 ∨ i = j + 3 ∨ j + 5 ≤ i := by omega
      rcases hd with rfl | rfl | hdij
      · exact (adjA c3 (by omega)).symm
      · exact (c3.claimD_odd hXY hB' hC hux2 (by omega) hjpar).symm
      · exact c3.e_rev hXY hB' hC hux2 hi hipar hj hjpar hdij
  · exact c3.e_z hXY hB' hC hux2 hi hipar

end Case3Data

end JSP415
