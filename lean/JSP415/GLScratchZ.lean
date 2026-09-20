import JSP415.GLIface
import JSP415.GLScratchD

/-!
# Coordinator file: the case-(iii) assembly

`case3_finale`: from `InternalFacts` (E+F, agent T2) and `LeftoverFacts`
(C+G+H, agent T3), build the two-block decomposition of the red graph and
feed it to `two_block_ramsey` (GLScratchD).
-/

open Finset
open Classical

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

namespace Case3Data

/-- `S1U ∪ S2U` is exactly the `Y`-side of `S`. -/
theorem S1U_union_S2U (c3 : Case3Data G X Y) :
    c3.S1U ∪ c3.S2U = (c3.S.toFinset).filter (· ∈ Y) := by
  have h : (c3.A ++ [c3.z]).toFinset ∪ (c3.z :: c3.B).toFinset =
      (c3.A ++ c3.z :: c3.B).toFinset := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_union, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  unfold S1U S2U S1 S2 S
  rw [← Finset.filter_union, h]

/-- `sc1 ∪ sc2` is exactly `Y \ S`. -/
theorem sc1_union_sc2 (c3 : Case3Data G X Y) :
    c3.sc1 ∪ c3.sc2 = Y \ c3.S.toFinset := by
  ext w
  simp only [sc1, sc2, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro hw
    by_cases h : G.Adj w c3.z
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨hw, h⟩

/-- `U1 ∪ U2 = Y`. -/
theorem U1_union_U2 (c3 : Case3Data G X Y) : c3.U1 ∪ c3.U2 = Y := by
  have e : c3.U1 ∪ c3.U2 =
      (c3.S1U ∪ c3.S2U) ∪ (c3.sc1 ∪ c3.sc2) := by
    unfold U1 U2; ext v; simp [Finset.mem_union]; tauto
  rw [e, S1U_union_S2U, sc1_union_sc2]
  ext v
  simp only [Finset.mem_union, Finset.mem_filter, List.mem_toFinset,
    Finset.mem_sdiff]
  constructor
  · rintro (⟨-, hv⟩ | ⟨hv, -⟩) <;> exact hv
  · intro hv
    by_cases h : v ∈ c3.S
    · exact Or.inl ⟨h, hv⟩
    · exact Or.inr ⟨hv, h⟩

/-- `L1 ∪ L2 = X`. -/
theorem L1_union_L2 (c3 : Case3Data G X Y) : c3.L1 ∪ c3.L2 = X := by
  unfold L1 L2 SL
  ext v
  simp only [Finset.mem_union, Finset.mem_filter, List.mem_toFinset,
    Finset.mem_sdiff]
  constructor
  · rintro (⟨-, hv⟩ | ⟨hv, -⟩) <;> exact hv
  · intro hv
    by_cases h : v ∈ c3.S
    · exact Or.inl ⟨h, hv⟩
    · exact Or.inr ⟨hv, h⟩

/-- `U1` and `U2` are disjoint. -/
theorem disjoint_U1_U2 (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    Disjoint c3.U1 c3.U2 := by
  obtain ⟨hzA, hzB, hAB⟩ := c3.hb.disjoint_pieces
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  rcases Finset.mem_union.mp hv1 with hv1 | hv1 <;>
    rcases Finset.mem_union.mp hv2 with hv2 | hv2
  · -- `v ∈ S1U ∩ S2U`: impossible (`A`, `{z}`, `B` are disjoint pieces).
    obtain ⟨hvS1, hvY⟩ := Finset.mem_filter.mp hv1
    obtain ⟨hvS2, -⟩ := Finset.mem_filter.mp hv2
    rw [List.mem_toFinset] at hvS1 hvS2
    rcases List.mem_append.mp hvS1 with hvA | hvz
    · rcases List.mem_cons.mp hvS2 with rfl | hvB
      · exact hzA hvA
      · exact hAB hvA hvB
    · rw [List.mem_singleton] at hvz
      subst hvz
      rcases List.mem_cons.mp hvS2 with _ | hvB
      · exact (hXY.notMem_left c3.hz hvY).elim
      · exact hzB hvB
  · -- `v ∈ S1U ∩ sc2`: `v ∈ S` and `v ∉ S`.
    obtain ⟨hvS1, -⟩ := Finset.mem_filter.mp hv1
    obtain ⟨hv2', -⟩ := Finset.mem_filter.mp hv2
    obtain ⟨-, hvS⟩ := Finset.mem_sdiff.mp hv2'
    exact hvS (by
      rw [List.mem_toFinset] at hvS1
      rcases List.mem_append.mp hvS1 with hvA | hvz
      · exact List.mem_toFinset.mpr (List.mem_append_left _ hvA)
      · rw [List.mem_singleton] at hvz
        subst hvz
        exact List.mem_toFinset.mpr
          (List.mem_append_right _ (List.mem_cons_self)))
  · -- `v ∈ sc1 ∩ S2U`: `v ∉ S` and `v ∈ S`.
    obtain ⟨hv1', -⟩ := Finset.mem_filter.mp hv1
    obtain ⟨-, hvS⟩ := Finset.mem_sdiff.mp hv1'
    obtain ⟨hvS2, -⟩ := Finset.mem_filter.mp hv2
    rw [List.mem_toFinset] at hvS2
    exact hvS (List.mem_toFinset.mpr (by
      rcases List.mem_cons.mp hvS2 with rfl | hvB
      · exact List.mem_append_right _ (List.mem_cons_self)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hvB)))
  · -- `v ∈ sc1 ∩ sc2`: `Adj` and `¬Adj`.
    obtain ⟨-, hAdj⟩ := Finset.mem_filter.mp hv1
    obtain ⟨-, hnAdj⟩ := Finset.mem_filter.mp hv2
    exact hnAdj hAdj

/-- `L1` and `L2` are disjoint. -/
theorem disjoint_L1_L2 (c3 : Case3Data G X Y) : Disjoint c3.L1 c3.L2 := by
  unfold L1 L2 SL
  exact Finset.disjoint_left.mpr fun v hv hv2 ↦
    (Finset.mem_sdiff.mp hv2).2 (Finset.mem_filter.mp hv).1

end Case3Data

/-- The finale: internal + leftover facts give the Ramsey disjunction. -/
theorem case3_finale (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    (hEF : c3.InternalFacts) (hLF : c3.LeftoverFacts)
    {k ℓ : ℕ} (hkl : k ≠ ℓ)
    (hX : X.card = (k + ℓ + 1) / 2) (hY : Y.card = (k + ℓ + 1) / 2) :
    BipGoal G X Y k ℓ := by
  obtain ⟨hE1, hE2⟩ := hEF
  obtain ⟨hC, hCa, hG1, hG2, hH1, hH2⟩ := hLF
  refine two_block_ramsey hXY hkl hX hY
    c3.U1_union_U2 (c3.disjoint_U1_U2 hXY)
    c3.L1_union_L2 c3.disjoint_L1_L2 ?_ ?_ ?_ ?_
  · -- `U1 × L1` red: `S1U–SL` by E, `sc1–SL` by G₁.
    intro u hu l hl
    rcases Finset.mem_union.mp hu with huS | husc
    · exact hE1 u huS l hl
    · exact hG1 u husc l hl
  · -- `U2 × L2` red: `S2U–L2` by C-analogue, `sc2–L2` by H₂.
    intro u hu l hl
    rcases Finset.mem_union.mp hu with huS | husc
    · exact (hCa l hl u huS).symm
    · exact (hH2 l hl u husc).symm
  · -- `U1 × L2` blue: `S1U–L2` by C, `sc1–L2` by H₁.
    intro u hu l hl
    rcases Finset.mem_union.mp hu with huS | husc
    · exact fun hadj ↦ hC l hl u huS hadj.symm
    · exact fun hadj ↦ hH1 l hl u husc hadj.symm
  · -- `U2 × L1` blue: `S2U–SL` by E-analogue, `sc2–SL` by G₂.
    intro u hu l hl
    rcases Finset.mem_union.mp hu with huS | husc
    · exact hE2 u huS l hl
    · exact hG2 u husc l hl

end JSP415
