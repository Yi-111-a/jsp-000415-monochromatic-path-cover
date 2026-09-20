import JSP415.BipLemmas

open Finset

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Independent-route attempt at `bip_ramsey_path` (GL73 Thm 3)

Route: maximal either-order bipath (as in GL73). The hard case is when a
maximum bipath fails to cover `X ∪ Y`; GL's claims A–H then force a
"split" colouring (two complete bipartite red blocks, blue between
blocks), which settles the counting. The heavy lifting for the leftover
analysis is already in `BipLemmas` (the `bipathO_leftover_opp_of_*`
killing lemmas and the type-(iii) claim-A lemmas). -/

section Wlog

variable {G : SimpleGraph V} {X Y : Finset V}

/-- `Color.adjXY` is symmetric in the two sides. -/
theorem adjXY_swapXY {c : Color} {a b : V} :
    Color.adjXY G X Y c a b ↔ Color.adjXY G Y X c a b := by
  cases c <;> exact ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩

theorem isChain_swapXY {c : Color} {l : List V} :
    l.IsChain (Color.adjXY G X Y c) ↔ l.IsChain (Color.adjXY G Y X c) := by
  constructor <;> intro h <;> exact h.imp fun _ _ ↦ adjXY_swapXY.mp

theorem isBipath_swapXY {A : List V} {z : V} {B : List V} :
    IsBipath G X Y A z B ↔ IsBipath G Y X A z B := by
  simp only [IsBipath, isChain_swapXY]

theorem isBipathB_swapXY {A : List V} {z : V} {B : List V} :
    IsBipathB G X Y A z B ↔ IsBipathB G Y X A z B := by
  simp only [IsBipathB, isChain_swapXY]

theorem isBipathO_swapXY {A : List V} {z : V} {B : List V} :
    IsBipathO G X Y A z B ↔ IsBipathO G Y X A z B := by
  unfold IsBipathO
  rw [isBipath_swapXY, isBipathB_swapXY]

/-- An `IsBipath` in `G` is an `IsBipathB` in `Gᶜ`. -/
theorem IsBipath.to_complB {A : List V} {z : V} {B : List V}
    (hXY : Disjoint X Y) (h : IsBipath G X Y A z B) :
    IsBipathB Gᶜ X Y A z B :=
  ⟨h.1.imp fun _ _ hh ↦ Color.adjXY.to_compl_blue hXY hh,
   h.2.1.imp fun _ _ hh ↦ Color.adjXY.to_compl_red hXY hh, h.2.2⟩

/-- An `IsBipathB` in `Gᶜ` is an `IsBipath` in `G`. -/
theorem IsBipathB.of_compl' {A : List V} {z : V} {B : List V}
    (hXY : Disjoint X Y) (h : IsBipathB Gᶜ X Y A z B) :
    IsBipath G X Y A z B :=
  ⟨h.1.imp fun _ _ hh ↦ Color.adjXY.compl_blue hXY hh,
   h.2.1.imp fun _ _ hh ↦ Color.adjXY.compl_red hXY hh, h.2.2⟩

/-- Either-order bipaths in `G` and `Gᶜ` coincide. -/
theorem isBipathO_compl (hXY : Disjoint X Y) {A : List V} {z : V} {B : List V} :
    IsBipathO Gᶜ X Y A z B ↔ IsBipathO G X Y A z B := by
  unfold IsBipathO
  constructor
  · rintro (h | h)
    · exact Or.inr (IsBipath.of_compl hXY h)
    · exact Or.inl (IsBipathB.of_compl' hXY h)
  · rintro (h | h)
    · exact Or.inr (IsBipath.to_complB hXY h)
    · exact Or.inl (IsBipathB.to_compl hXY h)

/-- A `Gᶜ`-red chain across `X Y` is a `G`-blue chain. -/
theorem chain_blue_of_compl_red (hXY : Disjoint X Y) {l : List V}
    (h : l.IsChain (Color.adjXY Gᶜ X Y .red)) :
    l.IsChain (Color.adjXY G X Y .blue) :=
  h.imp fun _ _ hh ↦ Color.adjXY.compl_red hXY hh

/-- A `Gᶜ`-blue chain across `X Y` is a `G`-red chain. -/
theorem chain_red_of_compl_blue (hXY : Disjoint X Y) {l : List V}
    (h : l.IsChain (Color.adjXY Gᶜ X Y .blue)) :
    l.IsChain (Color.adjXY G X Y .red) :=
  h.imp fun _ _ hh ↦ Color.adjXY.compl_blue hXY hh

end Wlog

end JSP415
