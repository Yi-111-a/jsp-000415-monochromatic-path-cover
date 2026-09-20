import JSP415.BipLemmas
open Finset
namespace JSP415
open bip_ramsey_path
variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
# `bip_ramsey_path_A` — Gyárfás–Lehel 1973 Thm 3 + Remark 1 (PVW24 Lemma 2.1)

Goal: disjoint `X Y`, `|X| = |Y| = (k+ℓ+1)/2`, `k ≠ ℓ` ⇒
∃ `VertPath`, red `Color.adjXY` chain on ≥ k+1 vertices or blue on ≥ ℓ+1.
-/

/-! ### Symmetry / complement transport -/

/-- `Color.adjXY` is symmetric in the two sides. -/
theorem adjXY_swapXY {G : SimpleGraph V} {X Y : Finset V} {c : Color} {a b : V} :
    Color.adjXY G X Y c a b ↔ Color.adjXY G Y X c a b := by
  cases c <;> exact ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩

theorem isChain_swapXY {G : SimpleGraph V} {X Y : Finset V} {c : Color} {l : List V} :
    l.IsChain (Color.adjXY G X Y c) ↔ l.IsChain (Color.adjXY G Y X c) := by
  constructor <;> intro h <;> exact h.imp fun _ _ ↦ adjXY_swapXY.mp

theorem isBipath_swapXY {G : SimpleGraph V} {X Y : Finset V} {A : List V} {z : V}
    {B : List V} : IsBipath G X Y A z B ↔ IsBipath G Y X A z B := by
  simp only [IsBipath, isChain_swapXY]

theorem isBipathB_swapXY {G : SimpleGraph V} {X Y : Finset V} {A : List V} {z : V}
    {B : List V} : IsBipathB G X Y A z B ↔ IsBipathB G Y X A z B := by
  simp only [IsBipathB, isChain_swapXY]

theorem isBipathO_swapXY {G : SimpleGraph V} {X Y : Finset V} {A : List V} {z : V}
    {B : List V} : IsBipathO G X Y A z B ↔ IsBipathO G Y X A z B := by
  unfold IsBipathO
  rw [isBipath_swapXY, isBipathB_swapXY]

/-- An `IsBipath` in `G` is an `IsBipathB` in `Gᶜ` (colours swap). -/
theorem IsBipath.to_complB {G : SimpleGraph V} {X Y : Finset V} (hXY : Disjoint X Y)
    {A : List V} {z : V} {B : List V} (h : IsBipath G X Y A z B) :
    IsBipathB Gᶜ X Y A z B :=
  ⟨h.1.imp fun _ _ hh ↦ Color.adjXY.to_compl_blue hXY hh,
   h.2.1.imp fun _ _ hh ↦ Color.adjXY.to_compl_red hXY hh, h.2.2⟩

/-- An `IsBipathB` in `Gᶜ` is an `IsBipath` in `G`. -/
theorem IsBipathB.of_compl' {G : SimpleGraph V} {X Y : Finset V} (hXY : Disjoint X Y)
    {A : List V} {z : V} {B : List V} (h : IsBipathB Gᶜ X Y A z B) :
    IsBipath G X Y A z B :=
  ⟨h.1.imp fun _ _ hh ↦ Color.adjXY.compl_blue hXY hh,
   h.2.1.imp fun _ _ hh ↦ Color.adjXY.compl_red hXY hh, h.2.2⟩

/-- Either-order bipaths in `G` and `Gᶜ` coincide. -/
theorem isBipathO_compl {G : SimpleGraph V} {X Y : Finset V} (hXY : Disjoint X Y)
    {A : List V} {z : V} {B : List V} :
    IsBipathO Gᶜ X Y A z B ↔ IsBipathO G X Y A z B := by
  unfold IsBipathO
  constructor
  · rintro (h | h)
    · exact Or.inr (IsBipath.of_compl hXY h)
    · exact Or.inl (IsBipathB.of_compl' hXY h)
  · rintro (h | h)
    · exact Or.inr (IsBipath.to_complB hXY h)
    · exact Or.inl (IsBipathB.to_compl hXY h)

/-- A `Gᶜ`-red chain is a `G`-blue chain. -/
theorem chain_blue_of_compl_red {G : SimpleGraph V} {X Y : Finset V} (hXY : Disjoint X Y)
    {l : List V} (h : l.IsChain (Color.adjXY Gᶜ X Y .red)) :
    l.IsChain (Color.adjXY G X Y .blue) :=
  h.imp fun _ _ hh ↦ Color.adjXY.compl_red hXY hh

/-- A `Gᶜ`-blue chain is a `G`-red chain. -/
theorem chain_red_of_compl_blue {G : SimpleGraph V} {X Y : Finset V} (hXY : Disjoint X Y)
    {l : List V} (h : l.IsChain (Color.adjXY Gᶜ X Y .blue)) :
    l.IsChain (Color.adjXY G X Y .red) :=
  h.imp fun _ _ hh ↦ Color.adjXY.compl_blue hXY hh

/-! ### Side-counting for `acrossXY` chains -/

variable {X Y : Finset V}

theorem acrossXY.right_mem_iff {a b : V} (hXY : Disjoint X Y)
    (h : acrossXY X Y a b) : a ∈ Y ↔ b ∈ X :=
  (acrossXY.left_mem_iff hXY (acrossXY.symm h)).symm

theorem acrossXY.next_mem_iff {l : List V}
    (h : l.IsChain (acrossXY X Y)) (hXY : Disjoint X Y) {i : ℕ}
    (hi : i + 1 < l.length) :
    (l[i] ∈ X ↔ l[i+1] ∈ Y) ∧ (l[i] ∈ Y ↔ l[i+1] ∈ X) := by
  have hedge : acrossXY X Y l[i] l[i+1] := by
    rw [List.isChain_iff_getElem] at h
    exact h i hi
  exact ⟨acrossXY.left_mem_iff hXY hedge, acrossXY.right_mem_iff hXY hedge⟩

/-- Every element of an `acrossXY` chain of length ≥ 2 lies in `X ∪ Y`. -/
theorem across_chain_mem_union (hXY : Disjoint X Y) {l : List V}
    (h : l.IsChain (acrossXY X Y)) {a : V} (ha : a ∈ l)
    (hlen : 2 ≤ l.length) : a ∈ X ∪ Y := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  rcases Nat.lt_or_ge i (l.length - 1) with hi' | hi'
  · have hedge : acrossXY X Y l[i] l[i + 1] := by
      rw [List.isChain_iff_getElem] at h
      exact h i (by omega)
    exact hedge.elim (fun h' ↦ Finset.mem_union_left _ h'.1)
      (fun h' ↦ Finset.mem_union_right _ h'.1)
  · have hedge : acrossXY X Y l[i - 1] l[i] := by
      rw [List.isChain_iff_getElem] at h
      convert h (i - 1) (by omega) using 2
      omega
    exact hedge.elim (fun h' ↦ Finset.mem_union_right _ h'.2)
      (fun h' ↦ Finset.mem_union_left _ h'.2)

/-- The whole vertex list of a bipath is an `acrossXY` chain (colours may
differ — every consecutive pair still crosses the bipartition). -/
theorem IsBipath.acrossChain {G : SimpleGraph V} {A : List V} {z : V} {B : List V}
    (hb : IsBipath G X Y A z B) : (A ++ z :: B).IsChain (acrossXY X Y) := by
  obtain ⟨hred, hblue, -⟩ := hb
  have hac1 : (A ++ [z]).IsChain (acrossXY X Y) :=
    hred.imp fun _ _ hh ↦ Color.adjXY.across hh
  have hac2 : (z :: B).IsChain (acrossXY X Y) :=
    hblue.imp fun _ _ hh ↦ Color.adjXY.across hh
  have hT : A ++ z :: B = (A ++ [z]) ++ B := by simp
  rw [hT, List.isChain_append]
  refine ⟨hac1, hac2.tail, fun x hx y hy ↦ ?_⟩
  rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
    List.getLast?_singleton, Option.mem_some_iff] at hx
  subst hx
  cases B with
  | nil => simp at hy
  | cons b t =>
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact (List.isChain_cons.mp hac2).1 b (by simp)

/-- Number of elements of a list in a finset, as an integer. -/
private def sideCount (S : Finset V) (l : List V) : ℤ :=
  (l.filter (· ∈ S)).length

private theorem sideCount_cons (S : Finset V) (a : V) (t : List V) :
    sideCount S (a :: t) = (if a ∈ S then 1 else 0) + sideCount S t := by
  unfold sideCount
  rw [List.filter_cons]
  by_cases ha : a ∈ S <;> simp [ha] <;> omega

/-- In an `acrossXY` chain whose elements lie in `X ∪ Y`, side counts sum to
the length. -/
theorem across_chain_side_sum (hXY : Disjoint X Y) :
    ∀ l : List V, l.IsChain (acrossXY X Y) → (∀ a ∈ l, a ∈ X ∪ Y) →
      sideCount X l + sideCount Y l = l.length := by
  intro l h hmem
  induction l with
  | nil => simp [sideCount]
  | cons a t iht =>
    have hta := iht h.tail (fun b hb ↦ hmem b (List.mem_cons_of_mem _ hb))
    rw [sideCount_cons, sideCount_cons, List.length_cons]
    have ha := hmem a (by simp)
    rcases Finset.mem_union.mp ha with haX | haY
    · have haY' : a ∉ Y := Disjoint.notMem_left hXY haX
      simp only [haX, haY', ite_true, ite_false]; push_cast; omega
    · have haX' : a ∉ X := Disjoint.notMem_right hXY haY
      simp only [haX', haY, ite_true, ite_false]; push_cast; omega

/-- In an `acrossXY` chain whose elements lie in `X ∪ Y`, the side counts
differ by at most one, conditioned on the head's side. -/
theorem across_chain_side_diff (hXY : Disjoint X Y) :
    ∀ l : List V, l.IsChain (acrossXY X Y) → (∀ a ∈ l, a ∈ X ∪ Y) →
      (∀ a ∈ l.head?, a ∈ X →
        sideCount X l - sideCount Y l = 0 ∨ sideCount X l - sideCount Y l = 1) ∧
      (∀ a ∈ l.head?, a ∈ Y →
        sideCount X l - sideCount Y l = 0 ∨ sideCount X l - sideCount Y l = -1) := by
  intro l h hmem
  induction l with
  | nil => exact ⟨fun a ha ↦ absurd ha (by simp), fun a ha ↦ absurd ha (by simp)⟩
  | cons a t iht =>
    have hta := iht h.tail (fun b hb ↦ hmem b (List.mem_cons_of_mem _ hb))
    constructor
    · intro x hx haX
      rw [List.head?_cons, Option.mem_some] at hx
      subst hx
      cases t with
      | nil =>
        right
        have haY : a ∉ Y := Finset.disjoint_left.mp hXY haX
        simp [sideCount, List.filter, haX, haY]
      | cons b s =>
        have hab : acrossXY X Y a b :=
          (List.isChain_cons.mp h).1 _ (by simp)
        have hbY : b ∈ Y := (acrossXY.left_mem_iff hXY hab).mp haX
        have hbX : b ∉ X := Disjoint.notMem_right hXY hbY
        have haY : a ∉ Y := Disjoint.notMem_left hXY haX
        have e : sideCount X (a :: b :: s) - sideCount Y (a :: b :: s)
            = sideCount X (b :: s) - sideCount Y (b :: s) + 1 := by
          simp only [sideCount_cons, haX, haY, hbX, hbY, ite_true, ite_false]
          ring
        obtain hbs | hbs := hta.2 b (by simp) hbY
        · right; rw [e, hbs]; ring
        · left; rw [e, hbs]; ring
    · intro x hx haY
      rw [List.head?_cons, Option.mem_some] at hx
      subst hx
      cases t with
      | nil =>
        right
        have haX : a ∉ X := Disjoint.notMem_right hXY haY
        simp [sideCount, List.filter, haX, haY]
      | cons b s =>
        have hab : acrossXY X Y a b :=
          (List.isChain_cons.mp h).1 _ (by simp)
        have hbX : b ∈ X := (acrossXY.right_mem_iff hXY hab).mp haY
        have hbY : b ∉ Y := Disjoint.notMem_left hXY hbX
        have haX : a ∉ X := Disjoint.notMem_right hXY haY
        have e : sideCount X (a :: b :: s) - sideCount Y (a :: b :: s)
            = sideCount X (b :: s) - sideCount Y (b :: s) - 1 := by
          simp only [sideCount_cons, haX, haY, hbX, hbY, ite_true, ite_false]
          ring
        obtain hbs | hbs := hta.1 b (by simp) hbX
        · right; rw [e, hbs]; ring
        · left; rw [e, hbs]; ring

/-- For a `Nodup` list, `sideCount` is the cardinality of the finset
intersection. -/
theorem sideCount_eq_card (S : Finset V) {l : List V} (hnd : l.Nodup) :
    sideCount S l = ((l.toFinset ∩ S).card : ℤ) := by
  unfold sideCount
  have hsub : (l.filter (· ∈ S)).Nodup := hnd.filter _
  have heq : (l.filter (· ∈ S)).toFinset = l.toFinset ∩ S := by
    ext x
    simp [List.mem_toFinset, List.mem_filter]
  rw [← List.toFinset_card_of_nodup hsub, heq]

end JSP415
