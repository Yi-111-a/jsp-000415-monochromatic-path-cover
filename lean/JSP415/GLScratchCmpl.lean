import JSP415.GLIface
import JSP415.GLScratchA   -- complement / swap lemmas (isBipathO_compl, ...)

open Finset
open Classical
namespace JSP415
open bip_ramsey_path
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

/-!
# `GLScratchCmpl` — the complement trick for the case-(iii) configuration

`Case3Data.compl` transports `Case3Data G X Y` to `Case3Data Gᶜ X Y` by
reversing the two branches (which swaps the red and blue roles): the `G`-red
branch `A ++ [z]` becomes the `Gᶜ`-blue branch `z :: A.reverse` and the
`G`-blue branch `z :: B` becomes the `Gᶜ`-red branch `B.reverse ++ [z]`.

We then identify the associated finsets (`S1U`, `S2U`, `SL`, `L2`) and the
predicate `HasUx2`, and transport the internal/cross claims:

* `claimE'_of_compl` : `ClaimE` of the complement gives `ClaimE'`.
* `claimF1_of_compl` : the complemented `F2` gives `F1`.
* `claimF2_of_compl` : the complemented `F1` gives `F2`.
-/

namespace Case3Data

/-- The complemented case-(iii) configuration.  `IsBipath G X Y A z B` becomes
`IsBipath Gᶜ X Y B.reverse z A.reverse`: the `Gᶜ`-red branch
`B.reverse ++ [z] = (z :: B).reverse` comes from the `G`-blue chain `z :: B`
via `Color.adjXY.to_compl_red`, and the `Gᶜ`-blue branch
`z :: A.reverse = (A ++ [z]).reverse` comes from the `G`-red chain `A ++ [z]`
via `Color.adjXY.to_compl_blue`.  Maximality transports through
`isBipathO_compl`. -/
def compl (c3 : Case3Data G X Y) (hXY : Disjoint X Y) : Case3Data Gᶜ X Y where
  A := c3.B.reverse
  z := c3.z
  B := c3.A.reverse
  hb := by
    obtain ⟨hred, hblue, hnd⟩ := c3.hb
    refine ⟨?_, ?_, ?_⟩
    · -- `B.reverse ++ [z] = (z :: B).reverse` is a `Gᶜ`-red chain.
      have h1 : (c3.z :: c3.B).reverse.IsChain (Color.adjXY G X Y .blue) :=
        Color.adjXY.isChain_reverse hblue
      have h2 : (c3.z :: c3.B).reverse.IsChain (Color.adjXY Gᶜ X Y .red) :=
        h1.imp fun _ _ hh ↦ Color.adjXY.to_compl_red hXY hh
      have heq : (c3.z :: c3.B).reverse = c3.B.reverse ++ [c3.z] := by simp
      rwa [heq] at h2
    · -- `z :: A.reverse = (A ++ [z]).reverse` is a `Gᶜ`-blue chain.
      have h1 : (c3.A ++ [c3.z]).reverse.IsChain (Color.adjXY G X Y .red) :=
        Color.adjXY.isChain_reverse hred
      have h2 : (c3.A ++ [c3.z]).reverse.IsChain (Color.adjXY Gᶜ X Y .blue) :=
        h1.imp fun _ _ hh ↦ Color.adjXY.to_compl_blue hXY hh
      have heq : (c3.A ++ [c3.z]).reverse = c3.z :: c3.A.reverse := by simp
      rwa [heq] at h2
    · -- `B.reverse ++ z :: A.reverse = (A ++ z :: B).reverse` is `Nodup`.
      have heq : c3.B.reverse ++ c3.z :: c3.A.reverse =
          (c3.A ++ c3.z :: c3.B).reverse := by simp
      rw [heq, List.nodup_reverse]
      exact hnd
  hmax := by
    intro A' z' B' h
    have h' : IsBipathO G X Y A' z' B' := (isBipathO_compl hXY).mp h
    have hle := c3.hmax A' z' B' h'
    simp only [bipathLen, List.length_reverse] at hle ⊢
    omega
  hz := c3.hz
  hA := by rw [List.reverse_ne_nil_iff]; exact c3.hB
  hB := by rw [List.reverse_ne_nil_iff]; exact c3.hA
  hhead := by
    rw [List.head_reverse]
    exact c3.hlast
  hlast := by
    rw [List.getLast_reverse]
    exact c3.hhead
  ux := c3.ux
  hux := by
    refine ⟨c3.hux.1, ?_⟩
    have heq : c3.B.reverse ++ c3.z :: c3.A.reverse =
        (c3.A ++ c3.z :: c3.B).reverse := by simp
    rw [heq, List.mem_reverse]
    exact c3.hux.2

/-! ### List and finset identifications for `c3.compl` -/

/-- The `S₁` list of the complemented data is `(z :: B).reverse`. -/
theorem c3c_S1 (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    (c3.compl hXY).S1 = (c3.z :: c3.B).reverse := by
  show c3.B.reverse ++ [c3.z] = (c3.z :: c3.B).reverse
  simp

/-- The `S₂` list of the complemented data is `(A ++ [z]).reverse`. -/
theorem c3c_S2 (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    (c3.compl hXY).S2 = (c3.A ++ [c3.z]).reverse := by
  show c3.z :: c3.A.reverse = (c3.A ++ [c3.z]).reverse
  simp

/-- The full vertex list of the complemented data is `(A ++ z :: B).reverse`. -/
theorem c3c_S (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    (c3.compl hXY).S = (c3.A ++ c3.z :: c3.B).reverse := by
  show c3.B.reverse ++ c3.z :: c3.A.reverse = (c3.A ++ c3.z :: c3.B).reverse
  simp

/-- The complemented `S₁`-uppers are the original `S₂`-uppers. -/
theorem c3c_S1U (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    (c3.compl hXY).S1U = c3.S2U := by
  show ((c3.compl hXY).S1.toFinset).filter (· ∈ Y) =
    ((c3.z :: c3.B).toFinset).filter (· ∈ Y)
  rw [c3c_S1 c3 hXY, List.toFinset_reverse]

/-- The complemented `S₂`-uppers are the original `S₁`-uppers. -/
theorem c3c_S2U (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    (c3.compl hXY).S2U = c3.S1U := by
  show ((c3.compl hXY).S2.toFinset).filter (· ∈ Y) =
    ((c3.A ++ [c3.z]).toFinset).filter (· ∈ Y)
  rw [c3c_S2 c3 hXY, List.toFinset_reverse]

/-- The complemented lower vertices are the original lower vertices. -/
theorem c3c_SL (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    (c3.compl hXY).SL = c3.SL := by
  show ((c3.compl hXY).S.toFinset).filter (· ∈ X) =
    ((c3.A ++ c3.z :: c3.B).toFinset).filter (· ∈ X)
  rw [c3c_S c3 hXY, List.toFinset_reverse]

/-- The complemented lower leftovers are the original lower leftovers. -/
theorem c3c_L2 (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    (c3.compl hXY).L2 = c3.L2 := by
  show X \ (c3.compl hXY).S.toFinset = X \ (c3.A ++ c3.z :: c3.B).toFinset
  rw [c3c_S c3 hXY, List.toFinset_reverse]

/-- A second distinct lower leftover survives complementation. -/
theorem c3c_ux2 (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (h : c3.HasUx2) : (c3.compl hXY).HasUx2 := by
  obtain ⟨u₂, huX, humem, hne⟩ := h
  refine ⟨u₂, huX, ?_, hne⟩
  have heq : (c3.compl hXY).A ++ (c3.compl hXY).z :: (c3.compl hXY).B =
      (c3.A ++ c3.z :: c3.B).reverse := by
    show c3.B.reverse ++ c3.z :: c3.A.reverse = (c3.A ++ c3.z :: c3.B).reverse
    simp
  rw [heq, List.mem_reverse]
  exact humem

/-! ### Transport of the internal and cross claims -/

/-- **Claim E′ from complemented Claim E.**  `ClaimE (c3c)` says every
`Y`-side vertex of `S₂` is `Gᶜ`-adjacent — i.e. non-`G`-adjacent — to every
`X`-side vertex of `S` lying in `B ∪ {z}`; that is exactly `ClaimE' c3`. -/
theorem claimE'_of_compl (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hEc : (c3.compl hXY).ClaimE) : c3.ClaimE' := by
  intro u hu l hl hlb
  have hu' : u ∈ (c3.compl hXY).S1U := by rw [c3c_S1U c3 hXY]; exact hu
  have hl' : l ∈ (c3.compl hXY).SL := by rw [c3c_SL c3 hXY]; exact hl
  have hmem : l ∈ (c3.compl hXY).A ∨ l = (c3.compl hXY).z := by
    rcases hlb with h | h
    · exact Or.inl (List.mem_reverse.mpr h)
    · exact Or.inr h
  have hadj : Gᶜ.Adj u l := hEc u hu' l hl' hmem
  rw [SimpleGraph.compl_adj] at hadj
  exact hadj.2

/-- **Claim F1 from complemented Claim F2.**  `¬ Gᶜ.Adj l u` with `l ≠ u`
(from the disjoint sides `l ∈ X`, `u ∈ Y`) forces `G.Adj l u`, hence
`G.Adj u l`. -/
theorem claimF1_of_compl (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hF2c : ∀ l ∈ (c3.compl hXY).SL, l ∈ (c3.compl hXY).A →
      ∀ u ∈ (c3.compl hXY).S2U, ¬ Gᶜ.Adj l u) :
    ∀ u ∈ c3.S1U, ∀ l ∈ c3.SL, l ∈ c3.B → G.Adj u l := by
  intro u hu l hl hlb
  have hu' : u ∈ (c3.compl hXY).S2U := by rw [c3c_S2U c3 hXY]; exact hu
  have hl' : l ∈ (c3.compl hXY).SL := by rw [c3c_SL c3 hXY]; exact hl
  have hlA : l ∈ (c3.compl hXY).A := List.mem_reverse.mpr hlb
  have hnadj : ¬ Gᶜ.Adj l u := hF2c l hl' hlA u hu'
  rw [SimpleGraph.compl_adj] at hnadj
  push Not at hnadj
  have hlu : l ≠ u := by
    rintro rfl
    have hlf := Finset.mem_filter.mp hl
    have huf := Finset.mem_filter.mp hu
    exact Disjoint.notMem_left hXY hlf.2 huf.2
  exact (hnadj hlu).symm

/-- **Claim F2 from complemented Claim F1.**  `Gᶜ.Adj u l` gives
`¬ G.Adj u l`, hence `¬ G.Adj l u` by symmetry. -/
theorem claimF2_of_compl (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hF1c : ∀ u ∈ (c3.compl hXY).S1U, ∀ l ∈ (c3.compl hXY).SL,
      l ∈ (c3.compl hXY).B → Gᶜ.Adj u l) :
    ∀ l ∈ c3.SL, l ∈ c3.A → ∀ u ∈ c3.S2U, ¬ G.Adj l u := by
  intro l hl hlA u hu
  have hu' : u ∈ (c3.compl hXY).S1U := by rw [c3c_S1U c3 hXY]; exact hu
  have hl' : l ∈ (c3.compl hXY).SL := by rw [c3c_SL c3 hXY]; exact hl
  have hlB : l ∈ (c3.compl hXY).B := List.mem_reverse.mpr hlA
  have hadj : Gᶜ.Adj u l := hF1c u hu' l hl' hlB
  rw [SimpleGraph.compl_adj] at hadj
  exact fun h ↦ hadj.2 h.symm

end Case3Data

end JSP415
