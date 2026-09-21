import JSP415.GLIface
import JSP415.GLScratchA
import JSP415.GLScratchW
import JSP415.GLScratchZ
import JSP415.GLScratchT5

/-!
# `GLScratchTop` — the `bip_ramsey_of_facts` reduction

Assuming the case-(iii) facts `hfacts` (the `InternalFacts`/`LeftoverFacts`
conjunction supplied by the claims agents), we prove `BipGoal` for disjoint
`X Y` with `|X| = |Y| = (k+ℓ+1)/2`, `k ≠ ℓ`:

* `k = 0` or `ℓ = 0`: a singleton `VertPath` settles it.
* Take a maximal either-order bipath `S = A ++ z :: B`.
* `IsBipathB` moves to `Gᶜ`; `z ∈ Y` swaps `X ↔ Y`.  The remaining core
  lemma `bip_red_first_lower` handles a red-first bipath with `z ∈ X`.
* If `S` covers `X ∪ Y`, `bipath_cover` finishes.
* If `A = []` or `B = []`, maximality forces `Y ⊆ S` (any `Y`-leftover
  extends `S` in either colour), and side-counting then contradicts
  non-covering.
* Otherwise `A, B ≠ []`; side-counting at the endpoints decides whether a
  `Y`-leftover exists (then the killing lemmas apply) or an `X`-leftover
  exists with both endpoints in `Y` (type (iii): `Case3Data` + `hfacts` +
  `case3_finale`).
-/

open Finset
open Classical

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

/-- In an `acrossXY`-chain with all vertices in `X ∪ Y`, the signed excess
of `X`-vertices over `Y`-vertices equals `[head ∈ X] + [last ∈ X] - 1`. -/
theorem acrossChain_inter_card_diff (hXY : Disjoint X Y) :
    ∀ {l : List V} {a b : V}, l.IsChain (acrossXY X Y) → l.Nodup →
      (∀ x ∈ l, x ∈ X ∪ Y) → l.head? = some a → l.getLast? = some b →
      (((l.toFinset ∩ X).card : ℤ) - ((l.toFinset ∩ Y).card : ℤ)) =
        (if a ∈ X then (1 : ℤ) else 0) + (if b ∈ X then (1 : ℤ) else 0) - 1 := by
  intro l
  induction l with
  | nil => intro a b _ _ _ h _; simp at h
  | cons x t ih =>
    intro a b hch hnd hmem hx hy
    rw [List.head?_cons, Option.some_inj] at hx
    subst hx
    cases t with
    | nil =>
      rw [List.getLast?_singleton, Option.some_inj] at hy
      subst hy
      have haU := hmem x (by simp)
      have hsingle : [x].toFinset = {x} := by simp
      rw [hsingle]
      rcases Finset.mem_union.mp haU with haX | haY
      · have haY' : x ∉ Y := Disjoint.notMem_left hXY haX
        rw [Finset.singleton_inter_of_mem haX,
          Finset.singleton_inter_of_notMem haY', Finset.card_singleton,
          Finset.card_empty, if_pos haX]
        norm_num
      · have haX' : x ∉ X := Disjoint.notMem_right hXY haY
        rw [Finset.singleton_inter_of_notMem haX',
          Finset.singleton_inter_of_mem haY, Finset.card_singleton,
          Finset.card_empty, if_neg haX']
        norm_num
    | cons c s =>
      have hcy : (c :: s).getLast? = some b := by
        rwa [List.getLast?_cons_cons] at hy
      obtain ⟨hxs, hndt⟩ := List.nodup_cons.mp hnd
      have hmem' : ∀ w ∈ c :: s, w ∈ X ∪ Y :=
        fun w hw ↦ hmem w (List.mem_cons_of_mem _ hw)
      have ih' := ih hch.tail hndt hmem' rfl hcy
      have hac : acrossXY X Y x c := (List.isChain_cons.mp hch).1 c (by simp)
      rw [List.toFinset_cons]
      have hxniX : x ∉ (c :: s).toFinset ∩ X :=
        fun h ↦ hxs (List.mem_toFinset.mp (Finset.mem_inter.mp h).1)
      have hxniY : x ∉ (c :: s).toFinset ∩ Y :=
        fun h ↦ hxs (List.mem_toFinset.mp (Finset.mem_inter.mp h).1)
      by_cases haX : x ∈ X
      · have haY : x ∉ Y := Disjoint.notMem_left hXY haX
        have hcY : c ∈ Y := (acrossXY.left_mem_iff hXY hac).mp haX
        have hcX : c ∉ X := Disjoint.notMem_right hXY hcY
        rw [Finset.insert_inter_of_mem haX, Finset.card_insert_of_notMem hxniX,
          Finset.insert_inter_of_notMem haY, if_pos haX]
        rw [if_neg hcX] at ih'
        push_cast at ih' ⊢
        omega
      · have haY : x ∈ Y := by
          rcases Finset.mem_union.mp (hmem x (by simp)) with h | h
          · exact absurd h haX
          · exact h
        have hcX : c ∈ X := (acrossXY.right_mem_iff hXY hac).mp haY
        have hcY : c ∉ Y := Disjoint.notMem_left hXY hcX
        rw [Finset.insert_inter_of_notMem haX, Finset.insert_inter_of_mem haY,
          Finset.card_insert_of_notMem hxniY, if_neg haX]
        rw [if_pos hcX] at ih'
        push_cast at ih' ⊢
        omega

/-- If fewer than `|T|` elements of `l` lie in `T`, some `x ∈ T` misses `l`. -/
theorem exists_mem_notMem_of_inter_card_lt {l : List V} {T : Finset V}
    (h : (l.toFinset ∩ T).card < T.card) : ∃ x ∈ T, x ∉ l := by
  by_contra hcon
  push_neg at hcon
  have hsub : T ⊆ l.toFinset ∩ T :=
    fun x hx ↦ Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr (hcon x hx), hx⟩
  have := Finset.card_le_card hsub
  omega

/-- If `l`'s vertex set contains `|T|` elements of `T`, it contains `T`. -/
theorem subset_toFinset_of_inter_card {l : List V} {T : Finset V}
    (h : T.card ≤ (l.toFinset ∩ T).card) : T ⊆ l.toFinset := by
  have heq : l.toFinset ∩ T = T :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right h
  intro x hx
  rw [← heq] at hx
  exact (Finset.mem_inter.mp hx).1

/-- If `l` contains `|X|` vertices of `X` and `|Y|` vertices of `Y`,
it covers `X ∪ Y`. -/
theorem covers_of_inter_card_eq {l : List V} {X₁ Y₁ : Finset V}
    (h1 : (l.toFinset ∩ X₁).card = X₁.card)
    (h2 : (l.toFinset ∩ Y₁).card = Y₁.card) :
    ∀ v ∈ X₁ ∪ Y₁, v ∈ l := by
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · exact List.mem_toFinset.mp
      (subset_toFinset_of_inter_card (le_of_eq h1.symm) h)
  · exact List.mem_toFinset.mp
      (subset_toFinset_of_inter_card (le_of_eq h2.symm) h)

/-- A maximal either-order bipath has at least two vertices whenever `X` and
`Y` are both nonempty (any edge of the bipartite colouring gives one). -/
theorem bipathO_length_ge_two (H : SimpleGraph V) {X₁ Y₁ : Finset V}
    (hXY : Disjoint X₁ Y₁) {A : List V} {z : V} {B : List V}
    (hmax : ∀ A' z' B', IsBipathO H X₁ Y₁ A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B)
    {x y : V} (hx : x ∈ X₁) (hy : y ∈ Y₁) :
    2 ≤ (A ++ z :: B).length := by
  classical
  have hxy : acrossXY X₁ Y₁ x y := Or.inl ⟨hx, hy⟩
  rcases Color.adjXY_cases (G := H) hxy with h | h
  · have hbp : IsBipath H X₁ Y₁ [x] y [] := by
      refine ⟨?_, List.isChain_singleton _, ?_⟩
      · show ([x, y]).IsChain (Color.adjXY H X₁ Y₁ .red)
        rw [List.isChain_cons]
        refine ⟨fun w hw ↦ ?_, List.isChain_singleton _⟩
        simp only [List.head?_cons, Option.mem_some_iff] at hw
        subst hw; exact h
      · exact List.nodup_cons.mpr
          ⟨fun hm ↦ absurd (List.mem_singleton.mp hm) (acrossXY.ne hXY h.1),
            List.nodup_singleton _⟩
    have hle := hmax _ _ _ (Or.inl hbp)
    simp only [bipathLen, List.length_append, List.length_cons, List.length_nil]
      at hle ⊢
    omega
  · have hbp : IsBipath H X₁ Y₁ [] x [y] := by

      refine ⟨List.isChain_singleton _, ?_, ?_⟩
      · show ([x, y]).IsChain (Color.adjXY H X₁ Y₁ .blue)
        rw [List.isChain_cons]
        refine ⟨fun w hw ↦ ?_, List.isChain_singleton _⟩
        simp only [List.head?_cons, Option.mem_some_iff] at hw
        subst hw; exact h
      · exact List.nodup_cons.mpr
          ⟨fun hm ↦ absurd (List.mem_singleton.mp hm) (acrossXY.ne hXY h.1),
            List.nodup_singleton _⟩
    have hle := hmax _ _ _ (Or.inl hbp)
    simp only [bipathLen, List.length_append, List.length_cons, List.length_nil]
      at hle ⊢
    omega

/-- The core of the GL argument: a *maximal* red-first bipath
`S = A ++ z :: B` with midpoint `z ∈ X₁` settles the Ramsey alternative. -/
theorem bip_red_first_lower
    (hfacts : ∀ (H' : SimpleGraph V) {X₂ Y₂ : Finset V}, Disjoint X₂ Y₂ →
      ∀ c3 : Case3Data H' X₂ Y₂, c3.HasUx2 → c3.InternalFacts ∧ c3.LeftoverFacts)
    (htight : ∀ (H' : SimpleGraph V) {X₂ Y₂ : Finset V},
      ∀ c3 : Case3Data H' X₂ Y₂, Disjoint X₂ Y₂ → ¬ c3.HasUx2 →
      ∀ {k ℓ : ℕ} (hkl : k ≠ ℓ),
        X₂.card = (k + ℓ + 1) / 2 → Y₂.card = (k + ℓ + 1) / 2 →
        BipGoal H' X₂ Y₂ k ℓ)
    (H : SimpleGraph V) {X₁ Y₁ : Finset V} (hXY : Disjoint X₁ Y₁)
    {k ℓ : ℕ} (hkl : k ≠ ℓ)
    (hX : X₁.card = (k + ℓ + 1) / 2) (hY : Y₁.card = (k + ℓ + 1) / 2)
    {A : List V} {z : V} {B : List V}
    (hb : IsBipath H X₁ Y₁ A z B)
    (hmax : ∀ A' z' B', IsBipathO H X₁ Y₁ A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B)
    (hz : z ∈ X₁) :
    BipGoal H X₁ Y₁ k ℓ := by
  classical
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (show 0 < X₁.card by omega)
  obtain ⟨y₀, hy₀⟩ := Finset.card_pos.mp (show 0 < Y₁.card by omega)
  have hlen2 : 2 ≤ (A ++ z :: B).length := bipathO_length_ge_two H hXY hmax hx₀ hy₀
  have hch : (A ++ z :: B).IsChain (acrossXY X₁ Y₁) := IsBipath.acrossChain hb
  have hnd : (A ++ z :: B).Nodup := hb.2.2
  have hmem : ∀ a ∈ A ++ z :: B, a ∈ X₁ ∪ Y₁ :=
    fun a ha ↦ across_chain_mem_union hXY hch ha hlen2
  by_cases hcov : ∀ v ∈ X₁ ∪ Y₁, v ∈ A ++ z :: B
  · exact bipath_cover hb hcov (by
      have hcard : (X₁ ∪ Y₁).card = (k + ℓ + 1) / 2 + (k + ℓ + 1) / 2 := by
        rw [Finset.card_union_of_disjoint hXY, hX, hY]
      omega)
  -- `S` does not cover `X ∪ Y`
  have hAB : A ≠ [] ∨ B ≠ [] := by
    by_contra h
    push_neg at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.length_cons, List.length_nil, List.nil_append] at hlen2
    omega
  by_cases hAe : A = []
  · ---------------------------------------------------------- A = []
    subst hAe
    simp only [List.nil_append] at hch hnd hmem hcov hlen2
    have hB : B ≠ [] := by
      rcases hAB with h | h
      · exact absurd rfl h
      · exact h
    -- every `Y`-leftover extends `S`, so `Y ⊆ S`
    have hYS : ∀ w ∈ Y₁, w ∈ z :: B := by
      intro w hwY
      by_contra hwS
      have hwz : acrossXY X₁ Y₁ w z := Or.inr ⟨hwY, hz⟩
      rcases Color.adjXY_cases (G := H) hwz with h | h
      · -- `w–z` red: `([w], z, B)` is a longer bipath
        have hbp : IsBipath H X₁ Y₁ [w] z B := by
          refine ⟨?_, hb.2.1, List.nodup_cons.mpr ⟨hwS, hb.2.2⟩⟩
          show ([w, z]).IsChain (Color.adjXY H X₁ Y₁ .red)
          rw [List.isChain_cons]
          refine ⟨fun y hy ↦ ?_, List.isChain_singleton _⟩
          simp only [List.head?_cons, Option.mem_some_iff] at hy
          subst hy; exact h
        exact absurd (hmax _ _ _ (Or.inl hbp)) (by simp only [bipathLen, List.length_append, List.length_cons, List.length_nil]; omega)
      · -- `w–z` blue: `([], w, z :: B)` is a longer bipath
        have hbp : IsBipath H X₁ Y₁ [] w (z :: B) := by
          refine ⟨List.isChain_singleton _, ?_,
            List.nodup_cons.mpr ⟨hwS, hb.2.2⟩⟩
          rw [List.isChain_cons]
          refine ⟨fun y hy ↦ ?_, hb.2.1⟩
          simp only [List.head?_cons, Option.mem_some_iff] at hy
          subst hy; exact h
        exact absurd (hmax _ _ _ (Or.inl hbp)) (by simp only [bipathLen, List.length_append, List.length_cons, List.length_nil]; omega)
    have hYsub : Y₁ ⊆ (z :: B).toFinset :=
      fun w hw ↦ List.mem_toFinset.mpr (hYS w hw)
    have hYeq : (z :: B).toFinset ∩ Y₁ = Y₁ :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right
        (Finset.card_le_card
          (fun w hw ↦ Finset.mem_inter.mpr ⟨hYsub hw, hw⟩))
    have hcY : ((z :: B).toFinset ∩ Y₁).card = (k + ℓ + 1) / 2 := by
      rw [hYeq]; exact hY
    have hlast? : (z :: B).getLast? = some (B.getLast hB) := by
      rw [getLast?_cons_ne_nil hB, List.getLast?_eq_getLast_of_ne_nil hB]
    have hdiff := acrossChain_inter_card_diff hXY hch hnd hmem rfl hlast?
    rw [if_pos hz] at hdiff
    have hcXle : ((z :: B).toFinset ∩ X₁).card ≤ (k + ℓ + 1) / 2 := by
      rw [← hX]; exact Finset.card_le_card Finset.inter_subset_right
    by_cases hbX : B.getLast hB ∈ X₁
    · rw [if_pos hbX] at hdiff
      exfalso; omega
    · rw [if_neg hbX] at hdiff
      have hcX : ((z :: B).toFinset ∩ X₁).card = (k + ℓ + 1) / 2 := by omega
      exfalso
      exact hcov (covers_of_inter_card_eq (l := z :: B) (by omega) (by omega))
  · by_cases hBe : B = []
    · ------------------------------------------------------ B = []
      subst hBe
      have hA : A ≠ [] := by
        rcases hAB with h | h
        · exact h
        · exact absurd rfl h
      -- every `Y`-leftover extends `S = A ++ [z]`, so `Y ⊆ S`
      have hYS : ∀ w ∈ Y₁, w ∈ A ++ [z] := by
        intro w hwY
        by_contra hwS
        have hwz : acrossXY X₁ Y₁ w z := Or.inr ⟨hwY, hz⟩
        rcases Color.adjXY_cases (G := H) hwz with h | h
        · -- `w–z` red: `(A ++ [z], w, [])` is a longer bipath
          have hbp : IsBipath H X₁ Y₁ (A ++ [z]) w [] := by
            refine ⟨?_, List.isChain_singleton _, ?_⟩
            · rw [List.isChain_append]
              refine ⟨hb.1, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
              rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
                List.getLast?_singleton, Option.mem_some_iff] at hx
              rw [List.head?_cons, Option.mem_some_iff] at hy
              subst hx; subst hy; exact Color.adjXY.symm h
            · have hp : List.Perm ((A ++ [z]) ++ w :: []) (w :: A ++ z :: []) :=
                List.perm_append_comm
              exact hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hwS, hb.2.2⟩)
          exact absurd (hmax _ _ _ (Or.inl hbp)) (by simp only [bipathLen, List.length_append, List.length_cons, List.length_nil]; omega)
        · -- `w–z` blue: `(A, z, [w])` is a longer bipath
          have hbp : IsBipath H X₁ Y₁ A z [w] := by
            refine ⟨hb.1, ?_, ?_⟩
            · show ([z, w]).IsChain (Color.adjXY H X₁ Y₁ .blue)
              rw [List.isChain_cons]
              refine ⟨fun y hy ↦ ?_, List.isChain_singleton _⟩
              simp only [List.head?_cons, Option.mem_some_iff] at hy
              subst hy; exact Color.adjXY.symm h
            · have hp : List.Perm (A ++ z :: [w]) (w :: A ++ z :: []) := by
                rw [show A ++ z :: [w] = (A ++ [z]) ++ [w] from
                  (List.append_assoc A [z] [w]).symm]
                exact List.perm_append_comm
              exact hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hwS, hb.2.2⟩)
          exact absurd (hmax _ _ _ (Or.inl hbp)) (by simp only [bipathLen, List.length_append, List.length_cons, List.length_nil]; omega)
      have hYsub : Y₁ ⊆ (A ++ z :: []).toFinset :=
        fun w hw ↦ List.mem_toFinset.mpr (hYS w hw)
      have hYeq : (A ++ z :: []).toFinset ∩ Y₁ = Y₁ :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right
          (Finset.card_le_card
            (fun w hw ↦ Finset.mem_inter.mpr ⟨hYsub hw, hw⟩))
      have hcY : ((A ++ z :: []).toFinset ∩ Y₁).card = (k + ℓ + 1) / 2 := by
        rw [hYeq]; exact hY
      have hhead? : (A ++ z :: []).head? = some (A.head hA) := by
        rw [List.head?_append_of_ne_nil _ hA, List.head?_eq_some_head hA]
      have hlast? : (A ++ z :: []).getLast? = some z := by
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
          List.getLast?_singleton]
      have hdiff := acrossChain_inter_card_diff hXY hch hnd hmem hhead? hlast?
      rw [if_pos hz] at hdiff
      have hcXle : ((A ++ z :: []).toFinset ∩ X₁).card ≤ (k + ℓ + 1) / 2 := by
        rw [← hX]; exact Finset.card_le_card Finset.inter_subset_right
      by_cases haX : A.head hA ∈ X₁
      · rw [if_pos haX] at hdiff
        exfalso; omega
      · rw [if_neg haX] at hdiff
        have hcX : ((A ++ z :: []).toFinset ∩ X₁).card = (k + ℓ + 1) / 2 := by
          omega
        exfalso
        exact hcov (covers_of_inter_card_eq (l := A ++ z :: [])
          (by omega) (by omega))
    · ---------------------------------------------- A ≠ [], B ≠ []
      have hhead? : (A ++ z :: B).head? = some (A.head hAe) := by
        rw [List.head?_append_of_ne_nil _ hAe, List.head?_eq_some_head hAe]
      have hlast? : (A ++ z :: B).getLast? = some (B.getLast hBe) := by
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
          getLast?_cons_ne_nil hBe, List.getLast?_eq_getLast_of_ne_nil hBe]
      have hdiff := acrossChain_inter_card_diff hXY hch hnd hmem hhead? hlast?
      have ha1U : A.head hAe ∈ X₁ ∪ Y₁ :=
        hmem _ (List.mem_append_left _ (List.head_mem hAe))
      have hbsU : B.getLast hBe ∈ X₁ ∪ Y₁ :=
        hmem _ (List.mem_append_right _
          (List.mem_cons_of_mem _ (List.getLast_mem hBe)))
      have hcXle : ((A ++ z :: B).toFinset ∩ X₁).card ≤ (k + ℓ + 1) / 2 := by
        rw [← hX]; exact Finset.card_le_card Finset.inter_subset_right
      have hcYle : ((A ++ z :: B).toFinset ∩ Y₁).card ≤ (k + ℓ + 1) / 2 := by
        rw [← hY]; exact Finset.card_le_card Finset.inter_subset_right
      rcases Finset.mem_union.mp ha1U with ha1X | ha1Y
      · rcases Finset.mem_union.mp hbsU with hbsX | hbsY
        · -- both endpoints in `X`: `|S∩X| = |S∩Y| + 1`, so a `Y`-leftover
          -- exists and is killed by the same-ends lemma
          rw [if_pos ha1X, if_pos hbsX] at hdiff
          obtain ⟨u, huY, huS⟩ := exists_mem_notMem_of_inter_card_lt
            (l := A ++ z :: B) (T := Y₁) (by omega)
          exact (bipathO_leftover_opp_of_same_ends hXY hb hmax huS hz huY
            hAe hBe ha1X hbsX).elim
        · -- across endpoints `a₁ ∈ X`, `bₛ ∈ Y`: `|S∩X| = |S∩Y|`; a
          -- `Y`-leftover exists (else `S` covers) and is killed
          rw [if_pos ha1X, if_neg (Disjoint.notMem_right hXY hbsY)] at hdiff
          have hcYlt : ((A ++ z :: B).toFinset ∩ Y₁).card < (k + ℓ + 1) / 2 := by
            by_contra hcon
            push_neg at hcon
            exact hcov (covers_of_inter_card_eq (l := A ++ z :: B)
              (by omega) (by omega))
          obtain ⟨u, huY, huS⟩ := exists_mem_notMem_of_inter_card_lt
            (l := A ++ z :: B) (T := Y₁) (by omega)
          exact (bipathO_leftover_opp_of_diff_ends hXY hb hmax huS hz huY
            hAe hBe (Or.inl ⟨ha1X, hbsY⟩)).elim
      · rcases Finset.mem_union.mp hbsU with hbsX | hbsY
        · -- across endpoints `a₁ ∈ Y`, `bₛ ∈ X`
          rw [if_neg (Disjoint.notMem_right hXY ha1Y), if_pos hbsX] at hdiff
          have hcYlt : ((A ++ z :: B).toFinset ∩ Y₁).card < (k + ℓ + 1) / 2 := by
            by_contra hcon
            push_neg at hcon
            exact hcov (covers_of_inter_card_eq (l := A ++ z :: B)
              (by omega) (by omega))
          obtain ⟨u, huY, huS⟩ := exists_mem_notMem_of_inter_card_lt
            (l := A ++ z :: B) (T := Y₁) (by omega)
          exact (bipathO_leftover_opp_of_diff_ends hXY hb hmax huS hz huY
            hAe hBe (Or.inr ⟨ha1Y, hbsX⟩)).elim
        · -- type (iii): both endpoints in `Y` → `X`-leftover → `Case3Data`
          rw [if_neg (Disjoint.notMem_right hXY ha1Y),
            if_neg (Disjoint.notMem_right hXY hbsY)] at hdiff
          obtain ⟨ux, huxX, huxS⟩ := exists_mem_notMem_of_inter_card_lt
            (l := A ++ z :: B) (T := X₁) (by omega)
          have c3 : Case3Data H X₁ Y₁ :=
            ⟨A, z, B, hb, hmax, hz, hAe, hBe, ha1Y, hbsY, ux, ⟨huxX, huxS⟩⟩
          by_cases hux2 : c3.HasUx2
          · obtain ⟨hEF, hLF⟩ := hfacts H hXY c3 hux2
            exact case3_finale hXY c3 hEF hLF hkl hX hY
          · exact htight H c3 hXY hux2 hkl hX hY

/-- The reduction lemma the coordinator wires into `bip_ramsey_path`:
given the internal/leftover facts for every `Case3Data`, the Ramsey
alternative follows. -/
theorem bip_ramsey_of_facts
    (hfacts : ∀ (H : SimpleGraph V) {X₁ Y₁ : Finset V}, Disjoint X₁ Y₁ →
      ∀ c3 : Case3Data H X₁ Y₁, c3.HasUx2 → c3.InternalFacts ∧ c3.LeftoverFacts)
    (htight : ∀ (H' : SimpleGraph V) {X₁ Y₁ : Finset V},
      ∀ c3 : Case3Data H' X₁ Y₁, Disjoint X₁ Y₁ → ¬ c3.HasUx2 →
      ∀ {k ℓ : ℕ} (hkl : k ≠ ℓ),
        X₁.card = (k + ℓ + 1) / 2 → Y₁.card = (k + ℓ + 1) / 2 →
        BipGoal H' X₁ Y₁ k ℓ)
    (hXY : Disjoint X Y)
    {k ℓ : ℕ} (hkl : k ≠ ℓ)
    (hX : X.card = (k + ℓ + 1) / 2) (hY : Y.card = (k + ℓ + 1) / 2) :
    BipGoal G X Y k ℓ := by
  classical
  obtain ⟨v, hvX⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
  obtain ⟨w₀, hwY⟩ := Finset.card_pos.mp (show 0 < Y.card by omega)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    obtain ⟨p, hch, hlen⟩ := bip_goal_singleton_red G X Y v
    exact ⟨p, Or.inl ⟨hch, hlen⟩⟩
  rcases Nat.eq_zero_or_pos ℓ with hl | hl
  · subst hl
    obtain ⟨p, hch, hlen⟩ := bip_goal_singleton_blue G X Y v
    exact ⟨p, Or.inr ⟨hch, hlen⟩⟩
  obtain ⟨A, z, B, hbo, hmax⟩ := exists_max_bipathO G X Y hXY v
  rcases hbo with hb | hbB
  · -- red-first maximal bipath
    have hlen2 : 2 ≤ (A ++ z :: B).length :=
      bipathO_length_ge_two G hXY hmax hvX hwY
    have hzU : z ∈ X ∪ Y :=
      across_chain_mem_union hXY (IsBipath.acrossChain hb)
        (List.mem_append_right _ List.mem_cons_self) hlen2
    rcases Finset.mem_union.mp hzU with hzX | hzY
    · exact bip_red_first_lower hfacts htight G hXY hkl hX hY hb hmax hzX
    · have hb' : IsBipath G Y X A z B := isBipath_swapXY.mp hb
      have hmax' : ∀ A' z' B', IsBipathO G Y X A' z' B' →
          bipathLen A' z' B' ≤ bipathLen A z B :=
        fun A' z' B' h ↦ hmax A' z' B' (isBipathO_swapXY.mpr h)
      exact bipGoal_swapXY
        (bip_red_first_lower hfacts htight G hXY.symm hkl hY hX hb' hmax' hzY)
  · -- blue-first maximal bipath: work in the complement with `ℓ k`
    have hb' : IsBipath Gᶜ X Y A z B := IsBipathB.to_compl hXY hbB
    have hmax' : ∀ A' z' B', IsBipathO Gᶜ X Y A' z' B' →
        bipathLen A' z' B' ≤ bipathLen A z B :=
      fun A' z' B' h ↦ hmax A' z' B' ((isBipathO_compl hXY).mp h)
    have hlen2 : 2 ≤ (A ++ z :: B).length :=
      bipathO_length_ge_two G hXY hmax hvX hwY
    have hzU : z ∈ X ∪ Y :=
      across_chain_mem_union hXY (IsBipath.acrossChain hb')
        (List.mem_append_right _ List.mem_cons_self) hlen2
    rcases Finset.mem_union.mp hzU with hzX | hzY
    · exact bipGoal_compl hXY
        (bip_red_first_lower hfacts htight Gᶜ hXY (Ne.symm hkl)
          (by omega) (by omega) hb' hmax' hzX)
    · have hb'' : IsBipath Gᶜ Y X A z B := isBipath_swapXY.mp hb'
      have hmax'' : ∀ A' z' B', IsBipathO Gᶜ Y X A' z' B' →
          bipathLen A' z' B' ≤ bipathLen A z B :=
        fun A' z' B' h ↦
          hmax A' z' B' ((isBipathO_compl hXY).mp (isBipathO_swapXY.mpr h))
      exact bipGoal_compl hXY (bipGoal_swapXY
        (bip_red_first_lower hfacts htight Gᶜ hXY.symm (Ne.symm hkl)
          (by omega) (by omega) hb'' hmax'' hzY))

end JSP415
