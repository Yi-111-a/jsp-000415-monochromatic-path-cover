import JSP415.BipLemmas

/-!
# Bipartite covering lemmas (PVW24 Lemmas 2.2–2.4)

Path-covering lemmas for bipartite graphs with degree conditions.
-/

open Finset

namespace JSP415

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace bip_cover

open bip_ramsey_path

variable {G : SimpleGraph V} [DecidableRel G.Adj] {X Y : Finset V}

/-! ### Basic neighbour/inclusion facts -/

/-- In a bipartite graph on `X ∪ Y`, neighbours of a `Y`-vertex lie in `X`. -/
theorem nbr_subset_X (hbip : BipartiteOn G X Y) {y : V} (hy : y ∈ Y) :
    G.neighborFinset y ⊆ X := by
  intro x hx
  rw [SimpleGraph.mem_neighborFinset] at hx
  rcases hbip.2 _ _ hx with h | h
  · exact absurd h.1 (bip_ramsey_path.Disjoint.notMem_right hbip.1 hy)
  · exact h.2

/-- In a bipartite graph on `X ∪ Y`, neighbours of an `X`-vertex lie in `Y`. -/
theorem nbr_subset_Y (hbip : BipartiteOn G X Y) {x : V} (hx : x ∈ X) :
    G.neighborFinset x ⊆ Y := by
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy
  rcases hbip.2 _ _ hy with h | h
  · exact h.2
  · exact absurd h.1 (bip_ramsey_path.Disjoint.notMem_left hbip.1 hx)

/-- Common-neighbour bound: two `Y`-vertices of degree `≥ (|X|+|Y|)/2`
share a neighbour outside any `S` with `|S| < |Y|`. -/
theorem common_nbr
    (hdeg : ∀ y ∈ Y, X.card + Y.card ≤ 2 * (G.neighborFinset y ∩ X).card)
    {y₁ y₂ : V} (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y) {S : Finset V} (hS : S.card < Y.card) :
    ∃ x ∈ X, x ∉ S ∧ G.Adj y₁ x ∧ G.Adj y₂ x := by
  have hAB : Y.card ≤
      ((G.neighborFinset y₁ ∩ X) ∩ (G.neighborFinset y₂ ∩ X)).card := by
    have h1 := Finset.card_union_add_card_inter
      (G.neighborFinset y₁ ∩ X) (G.neighborFinset y₂ ∩ X)
    have h2 : ((G.neighborFinset y₁ ∩ X) ∪ (G.neighborFinset y₂ ∩ X)).card ≤
        X.card := Finset.card_le_card
      (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
    have h3 := hdeg y₁ hy₁
    have h4 := hdeg y₂ hy₂
    omega
  obtain ⟨x, hx, hxS⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (lt_of_lt_of_le hS hAB)
  rw [Finset.mem_inter] at hx
  obtain ⟨hxA, hxB⟩ := hx
  rw [Finset.mem_inter] at hxA hxB
  refine ⟨x, hxA.2, hxS, ?_, ?_⟩
  · rw [← SimpleGraph.mem_neighborFinset]
    exact hxA.1
  · rw [← SimpleGraph.mem_neighborFinset]
    exact hxB.1

/-! ### `interleave` helpers for `G.Adj` chains -/

/-- `interleave` respects `G.Adj` when all cross pairs are adjacent. -/
theorem interleave_adj_chain {xs ys : List V}
    (h : ∀ a ∈ xs, ∀ b ∈ ys, G.Adj a b)
    (hle : xs.length ≤ ys.length + 1) (hge : ys.length ≤ xs.length) :
    (interleave xs ys).IsChain G.Adj :=
  interleave_isChain h (fun a ha b hb ↦ (h a ha b hb).symm) hle hge

/-- `interleave` is nodup when the two lists are nodup and land in
disjoint finsets. -/
theorem interleave_adj_nodup {xs ys : List V} {A B : Finset V} (hAB : Disjoint A B)
    (hxs : xs.Nodup) (hys : ys.Nodup)
    (hA : ∀ a ∈ xs, a ∈ A) (hB : ∀ b ∈ ys, b ∈ B) :
    (interleave xs ys).Nodup :=
  interleave_nodup hxs hys fun a ha hb ↦
    Finset.disjoint_left.mp hAB (hA a ha) (hB a hb)

/-- Appending one element to each list appends two elements to the
interleaved list (equal-length case). -/
theorem interleave_snoc {xs ys : List V} (h : xs.length = ys.length) (x y : V) :
    interleave (xs ++ [x]) (ys ++ [y]) = interleave xs ys ++ [x, y] := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b ys => simp at h
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [List.length_cons] at h
      have e : interleave ((a :: xs) ++ [x]) ((b :: ys) ++ [y]) =
          a :: b :: interleave (xs ++ [x]) (ys ++ [y]) := rfl
      rw [e, ih (by omega)]
      rfl

/-- Generic builder: an alternating `G.Adj`-chain from two lists whose
members live in disjoint finsets and are pairwise adjacent. -/
theorem mkAltPath {as bs : List V} {A B : Finset V} (hAB : Disjoint A B)
    (hA : ∀ a ∈ as, a ∈ A) (hB : ∀ b ∈ bs, b ∈ B)
    (hcomp : ∀ a ∈ as, ∀ b ∈ bs, G.Adj a b)
    (hle : as.length ≤ bs.length + 1) (hge : bs.length ≤ as.length)
    (hnx : as.Nodup) (hny : bs.Nodup) (hne : as ≠ []) :
    ∃ p : VertPath V, p.toList = interleave as bs ∧ p.toList.IsChain G.Adj :=
  ⟨⟨interleave as bs, interleave_ne_nil hne,
    interleave_adj_nodup hAB hnx hny hA hB⟩, rfl,
    interleave_adj_chain hcomp hle hge⟩

/-- Concatenation of two vertex-disjoint paths joined by an edge. -/
theorem mkAppendPath {p q : VertPath V} (hch1 : p.toList.IsChain G.Adj)
    (hch2 : q.toList.IsChain G.Adj)
    (hedge : ∀ a ∈ p.toList.getLast?, ∀ b ∈ q.toList.head?, G.Adj a b)
    (hdis : ∀ a ∈ p.toList, a ∉ q.toList) :
    ∃ r : VertPath V, r.toList = p.toList ++ q.toList ∧ r.toList.IsChain G.Adj :=
  ⟨⟨p.toList ++ q.toList,
    fun h ↦ p.nonempty (List.append_eq_nil_iff.mp h).1,
    List.nodup_append'.mpr ⟨p.nodup, q.nodup, hdis⟩⟩,
    rfl, List.isChain_append.mpr ⟨hch1, hch2, hedge⟩⟩

/-! ### Lemma 2.2: the extension argument -/

/-- **Lemma 2.2, list form.**  For each `k ≤ |Y|` there is an alternating
chain `x₁y₁…xₖyₖ` of `k` `X`-vertices and `k` `Y`-vertices. -/
theorem exists_alt_pair (hXY : Disjoint X Y)
    (hdeg : ∀ y ∈ Y, X.card + Y.card ≤ 2 * (G.neighborFinset y ∩ X).card)
    {k : ℕ} (hk : k ≤ Y.card) :
    ∃ xs ys : List V, xs.length = k ∧ ys.length = k ∧ xs.Nodup ∧ ys.Nodup ∧
      (∀ x ∈ xs, x ∈ X) ∧ (∀ y ∈ ys, y ∈ Y) ∧
      (interleave xs ys).IsChain G.Adj := by
  induction k with
  | zero =>
    refine ⟨[], [], rfl, rfl, List.nodup_nil, List.nodup_nil,
      fun _ h ↦ by simp at h, fun _ h ↦ by simp at h, ?_⟩
    show (interleave [] []).IsChain G.Adj
    simp [interleave]
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      -- start the path with a single `X`–`Y` edge
      obtain ⟨y, hy⟩ : Y.Nonempty := Finset.card_pos.mp (by omega)
      have hne : (G.neighborFinset y ∩ X).Nonempty := by
        rw [← Finset.card_pos]
        have h := hdeg y hy
        omega
      obtain ⟨x, hx⟩ := hne
      rw [Finset.mem_inter] at hx
      have hxy : G.Adj y x := by
        rw [← SimpleGraph.mem_neighborFinset]
        exact hx.1
      refine ⟨[x], [y], rfl, rfl, by simp, by simp,
        fun a ha ↦ by simp at ha; subst ha; exact hx.2,
        fun b hb ↦ by simp at hb; subst hb; exact hy, ?_⟩
      have e : interleave [x] [y] = [x, y] := rfl
      rw [e, List.isChain_cons]
      refine ⟨fun b hb ↦ ?_, List.isChain_singleton y⟩
      simp only [List.head?_singleton, Option.mem_some_iff] at hb
      subst hb
      exact hxy.symm
    · -- extend `x₁y₁…xₖyₖ` by a common neighbour of `yₖ` and a fresh `y'`
      obtain ⟨xs, ys, hxl, hyl, hnx, hny, hxs, hys, hch⟩ := ih (by omega)
      have hysne : ys ≠ [] := by
        intro h
        rw [h, List.length_nil] at hyl
        omega
      set yk := ys.getLast hysne with hyk
      have hykY : yk ∈ Y := hys _ (List.getLast_mem hysne)
      have hcard : ys.toFinset.card < Y.card := by
        rw [List.toFinset_card_of_nodup hny, hyl]; omega
      obtain ⟨y', hy'Y, hy'not⟩ : ∃ y' ∈ Y, y' ∉ ys := by
        obtain ⟨y', hy'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        exact ⟨y', hy'.1, fun h ↦ hy'.2 (List.mem_toFinset.mpr h)⟩
      obtain ⟨x', hx'X, hx'not, h1, h2⟩ :=
        common_nbr hdeg hykY hy'Y (S := xs.toFinset) (by
          rw [List.toFinset_card_of_nodup hnx, hxl]; omega)
      have hlast : (interleave xs ys).getLast? = some yk := by
        rw [interleave_getLast?_eq (hxl.trans hyl.symm)]
        exact List.getLast?_eq_getLast_of_ne_nil hysne
      refine ⟨xs ++ [x'], ys ++ [y'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hxl]
      · simp [hyl]
      · rw [List.nodup_append']
        refine ⟨hnx, List.nodup_singleton x', ?_⟩
        rw [List.disjoint_left]
        intro a ha hb
        rw [List.mem_singleton] at hb
        subst hb
        exact hx'not (List.mem_toFinset.mpr ha)
      · rw [List.nodup_append']
        refine ⟨hny, List.nodup_singleton y', ?_⟩
        rw [List.disjoint_left]
        intro a ha hb
        rw [List.mem_singleton] at hb
        subst hb
        exact hy'not ha
      · intro a ha
        rw [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hxs a ha
        · exact hx'X
      · intro b hb
        rw [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact hys b hb
        · exact hy'Y
      · rw [interleave_snoc (hxl.trans hyl.symm), List.isChain_append]
        refine ⟨hch, ?_, ?_⟩
        · rw [List.isChain_cons]
          refine ⟨fun b hb ↦ ?_, List.isChain_singleton y'⟩
          simp only [List.head?_singleton, Option.mem_some_iff] at hb
          subst hb
          exact h2.symm
        · intro a ha b hb
          rw [hlast, Option.mem_some_iff] at ha
          subst ha
          simp only [List.head?_cons, Option.mem_some_iff] at hb
          subst hb
          exact h1

/-- **Lemma 2.2 (internal form).**  If every vertex of `Y` has at least
`(|X|+|Y|)/2` neighbours inside `X`, a single path covers all of `Y` with
exactly `2|Y|` vertices. -/
theorem path_cover_aux (hXY : Disjoint X Y) (hY : Y.Nonempty)
    (hdeg : ∀ y ∈ Y, X.card + Y.card ≤ 2 * (G.neighborFinset y ∩ X).card) :
    ∃ p : VertPath V, p.toList.IsChain G.Adj ∧
      (∀ v ∈ p.toList, v ∈ X ∪ Y) ∧ (∀ y ∈ Y, y ∈ p) ∧
      p.toList.length = 2 * Y.card := by
  obtain ⟨xs, ys, hxl, hyl, hnx, hny, hxs, hys, hch⟩ :=
    exists_alt_pair hXY hdeg le_rfl
  have hlen : (interleave xs ys).length = 2 * Y.card := by
    rw [interleave_length, hxl, hyl]; ring
  have hcardys : ys.toFinset.card = Y.card := by
    rw [List.toFinset_card_of_nodup hny, hyl]
  have hfin : ys.toFinset = Y :=
    Finset.eq_of_subset_of_card_le
      (fun a ha ↦ hys a (List.mem_toFinset.mp ha)) hcardys.ge
  have hYpos : 0 < Y.card := hY.card_pos
  refine ⟨⟨interleave xs ys,
    List.ne_nil_of_length_pos (by omega),
    interleave_adj_nodup hXY hnx hny hxs hys⟩, hch, ?_, ?_, hlen⟩
  · intro v hv
    rw [mem_interleave] at hv
    rcases hv with hv | hv
    · exact Finset.mem_union.mpr (Or.inl (hxs v hv))
    · exact Finset.mem_union.mpr (Or.inr (hys v hv))
  · intro y hy
    show y ∈ interleave xs ys
    rw [mem_interleave]
    exact Or.inr (List.mem_toFinset.mp (hfin ▸ hy))

/-! ### Lemma 2.3: induction on `|X|` -/

/-- **Lemma 2.3 (internal form).**  If `|X| ≥ |Y| + 2m` and every `y ∈ Y`
has at least `|X| - m` neighbours inside `X`, then at most `⌊|X|/|Y|⌋`
paths cover all of `Y` and all but `|Y| + 2m` vertices of `X`.
Proved by strong induction on `|X|`. -/
theorem few_paths_aux (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ n : ℕ, ∀ X Y : Finset V, ∀ m : ℕ, X.card ≤ n →
    Disjoint X Y → 0 < Y.card → Y.card + 2 * m ≤ X.card →
    (∀ y ∈ Y, X.card - m ≤ (G.neighborFinset y ∩ X).card) →
    ∃ P : Finset (VertPath V),
      (∀ p ∈ P, p.toList.IsChain G.Adj) ∧
      (∀ p ∈ P, ∀ v ∈ p.toList, v ∈ X ∪ Y) ∧
      (∀ y ∈ Y, ∃ p ∈ P, y ∈ p) ∧
      P.card ≤ X.card / Y.card ∧
      (X \ P.biUnion VertPath.verts).card ≤ Y.card + 2 * m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X Y m hXn hXY hY hcard hdeg
    -- Lemma 2.2 applies: `|X| - m ≥ (|X|+|Y|)/2`.
    have hdeg2 : ∀ y ∈ Y, X.card + Y.card ≤ 2 * (G.neighborFinset y ∩ X).card := by
      intro y hy
      have h := hdeg y hy
      omega
    obtain ⟨p, hch, hmem, hYcov, hlen⟩ :=
      path_cover_aux hXY (Finset.card_pos.mp hY) hdeg2
    -- the path uses exactly `|Y|` vertices of `X`
    have hYpv : p.verts ∩ Y = Y := by
      ext a
      simp only [Finset.mem_inter]
      exact ⟨fun h ↦ h.2,
        fun ha ↦ ⟨VertPath.mem_verts.mpr (hYcov a ha), ha⟩⟩
    have hXcap : (X ∩ p.verts).card = Y.card := by
      have hsub : p.verts ⊆ X ∪ Y :=
        fun a ha ↦ hmem a (VertPath.mem_verts.mp ha)
      have hdisj : Disjoint (p.verts ∩ X) (p.verts ∩ Y) :=
        Finset.disjoint_left.mpr fun a ha hb ↦
          Finset.disjoint_left.mp hXY (Finset.mem_inter.mp ha).2
            (Finset.mem_inter.mp hb).2
      have hcard' : (p.verts ∩ X).card + (p.verts ∩ Y).card = p.verts.card := by
        rw [← Finset.card_union_of_disjoint hdisj]
        congr 1
        rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hsub]
      have hpc : p.verts.card = 2 * Y.card := by
        rw [VertPath.verts, List.toFinset_card_of_nodup p.nodup, hlen]
      rw [hYpv, hpc] at hcard'
      rw [Finset.inter_comm]
      omega
    have hX'card : (X \ p.verts).card = X.card - Y.card := by
      rw [Finset.card_sdiff, Finset.inter_comm, hXcap]
    by_cases hbase : (X \ p.verts).card ≤ Y.card + 2 * m
    · -- base case: the single path `p` suffices
      refine ⟨{p}, ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq
        rw [Finset.mem_singleton] at hq
        subst hq
        exact hch
      · intro q hq v hv
        rw [Finset.mem_singleton] at hq
        subst hq
        exact hmem v hv
      · intro y hy
        exact ⟨p, Finset.mem_singleton_self p, hYcov y hy⟩
      · rw [Finset.card_singleton, Nat.le_div_iff_mul_le hY]
        omega
      · rw [Finset.singleton_biUnion]
        omega
    · -- induction step: recurse on `X' = X ∖ V(p)`
      push Not at hbase
      have hX'Y : Disjoint (X \ p.verts) Y :=
        Disjoint.mono_left Finset.sdiff_subset hXY
      have hdeg' : ∀ y ∈ Y,
          (X \ p.verts).card - m ≤ (G.neighborFinset y ∩ (X \ p.verts)).card := by
        intro y hy
        have heq : G.neighborFinset y ∩ (X \ p.verts) =
            (G.neighborFinset y ∩ X) \ p.verts := by
          ext a
          simp only [Finset.mem_inter, Finset.mem_sdiff]
          tauto
        have hcard_le : ((G.neighborFinset y ∩ X) \ p.verts).card ≥
            (G.neighborFinset y ∩ X).card - Y.card := by
          rw [Finset.card_sdiff]
          have hle : (p.verts ∩ (G.neighborFinset y ∩ X)).card ≤ Y.card := by
            calc (p.verts ∩ (G.neighborFinset y ∩ X)).card
                ≤ (X ∩ p.verts).card := by
                  apply Finset.card_le_card
                  intro a ha
                  rw [Finset.mem_inter] at ha ⊢
                  exact ⟨Finset.mem_inter.mp ha.2 |>.2, ha.1⟩
              _ = Y.card := hXcap
          omega
        rw [heq]
        have hdegy := hdeg y hy
        omega
      obtain ⟨Q, hQch, hQmem, hQcov, hQcard, hQunc⟩ :=
        ih (X \ p.verts).card (by omega) (X \ p.verts) Y m le_rfl hX'Y hY
          (by omega) hdeg'
      refine ⟨insert p Q, ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact hch
        · exact hQch q hq
      · intro q hq v hv
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact hmem v hv
        · have h := hQmem q hq v hv
          rw [Finset.mem_union] at h ⊢
          rcases h with h | h
          · exact Or.inl (Finset.mem_sdiff.mp h).1
          · exact Or.inr h
      · intro y hy
        exact ⟨p, Finset.mem_insert_self p Q, hYcov y hy⟩
      · have hle : (insert p Q).card ≤ Q.card + 1 := Finset.card_insert_le p Q
        have hmul : Q.card * Y.card ≤ (X \ p.verts).card :=
          (Nat.le_div_iff_mul_le hY).mp hQcard
        rw [Nat.le_div_iff_mul_le hY]
        calc (insert p Q).card * Y.card ≤ (Q.card + 1) * Y.card :=
              Nat.mul_le_mul_right _ hle
          _ = Q.card * Y.card + Y.card := by rw [Nat.add_mul, one_mul]
          _ ≤ X.card := by omega
      · rw [Finset.biUnion_insert]
        have hset : X \ (p.verts ∪ Q.biUnion VertPath.verts) =
            (X \ p.verts) \ Q.biUnion VertPath.verts := by
          ext a
          simp only [Finset.mem_sdiff, Finset.mem_union]
          tauto
        rw [hset]
        exact hQunc

/-! ### Lemma 2.4 helpers -/

/-- Vertices of `A` adjacent to every vertex of `B`: the `X₀`/`Y₀` of
Lemma 2.4 phrased with adjacency rather than degree, so that the notion
restricts cleanly to subsets of `X` (which `fullNbr` does not, since it
counts neighbours in all of `G`). -/
def fullAdj (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    Finset V :=
  A.filter fun a ↦ B ⊆ G.neighborFinset a

theorem mem_fullAdj {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {a : V} :
    a ∈ fullAdj G A B ↔ a ∈ A ∧ B ⊆ G.neighborFinset a :=
  Finset.mem_filter

/-- A `fullAdj G A B`-vertex is adjacent to every vertex of `B`. -/
theorem fullAdj_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {a : V}
    (ha : a ∈ fullAdj G A B) {b : V} (hb : b ∈ B) : G.Adj a b := by
  have hb' : b ∈ G.neighborFinset a := (mem_fullAdj.mp ha).2 hb
  rwa [SimpleGraph.mem_neighborFinset] at hb'

/-- A bipartition can be viewed with the roles of `X` and `Y` swapped. -/
theorem bip_symm (h : BipartiteOn G X Y) : BipartiteOn G Y X :=
  ⟨h.1.symm, fun a b hab ↦ (h.2 a b hab).symm⟩

/-- On a bipartition, `fullAdj` coincides with `fullNbr` (a vertex of `X`
has all of `Y` as neighbours iff it has `|Y|` neighbours). -/
theorem fullNbr_iff_fullAdj (hbip : BipartiteOn G X Y) {a : V} (ha : a ∈ X) :
    a ∈ fullNbr G X Y ↔ a ∈ fullAdj G X Y := by
  have hsub : G.neighborFinset a ⊆ Y := nbr_subset_Y hbip ha
  constructor
  · intro h
    have hcard : (G.neighborFinset a).card = Y.card :=
      (Finset.mem_filter.mp h).2
    rw [mem_fullAdj]
    refine ⟨ha, fun b hb ↦ ?_⟩
    rw [Finset.eq_of_subset_of_card_le hsub hcard.ge]
    exact hb
  · intro h
    rw [mem_fullAdj] at h
    refine Finset.mem_filter.mpr ⟨ha, ?_⟩
    have heq : G.neighborFinset a = Y :=
      Finset.eq_of_subset_of_card_le hsub (Finset.card_le_card h.2)
    rw [heq]

/-- `fullNbr` and `fullAdj` agree as finsets on a bipartition. -/
theorem fullNbr_eq_fullAdj (hbip : BipartiteOn G X Y) :
    fullNbr G X Y = fullAdj G X Y ∧ fullNbr G Y X = fullAdj G Y X := by
  constructor
  · ext a
    by_cases ha : a ∈ X
    · exact fullNbr_iff_fullAdj hbip ha
    · exact ⟨fun h ↦ absurd (Finset.mem_filter.mp h).1 ha,
        fun h ↦ absurd (mem_fullAdj.mp h).1 ha⟩
  · ext a
    by_cases ha : a ∈ Y
    · exact fullNbr_iff_fullAdj (bip_symm hbip) ha
    · exact ⟨fun h ↦ absurd (Finset.mem_filter.mp h).1 ha,
        fun h ↦ absurd (mem_fullAdj.mp h).1 ha⟩

/-- For `xs` one element longer than `ys`, the interleaved list ends with
the last element of `xs`. -/
theorem interleave_getLast?_eq_left {xs ys : List V}
    (h : xs.length = ys.length + 1) :
    (interleave xs ys).getLast? = xs.getLast? := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have hxs : xs ≠ [] := by
        intro hcon
        simp only [hcon, List.length_nil, List.length_cons] at h
        omega
      rw [interleave, getLast?_cons_ne_nil (List.cons_ne_nil _ _),
        getLast?_cons_ne_nil (interleave_ne_nil hxs),
        getLast?_cons_ne_nil hxs,
        ih (by simp only [List.length_cons] at h ⊢; omega)]

/-- Finset version of `mkAltPath`: an alternating path through all vertices
of `S` and `T`, packaged with its vertex set, length and endpoints. -/
theorem mkAltPath_finset {A B S T : Finset V} (hAB : Disjoint A B)
    (hS : S ⊆ A) (hT : T ⊆ B)
    (hcomp : ∀ a ∈ S, ∀ b ∈ T, G.Adj a b)
    (hle : S.card ≤ T.card + 1) (hge : T.card ≤ S.card) (hSne : S.Nonempty) :
    ∃ p : VertPath V, p.toList.IsChain G.Adj ∧
      p.verts = S ∪ T ∧ p.toList.length = S.card + T.card ∧
      (∀ a ∈ p.toList.head?, a ∈ S) ∧
      (S.card = T.card + 1 → ∀ a ∈ p.toList.getLast?, a ∈ S) ∧
      (S.card = T.card → ∀ a ∈ p.toList.getLast?, a ∈ T) := by
  obtain ⟨p, hpl, hch⟩ := mkAltPath hAB
    (fun a ha ↦ hS (Finset.mem_toList.mp ha))
    (fun b hb ↦ hT (Finset.mem_toList.mp hb))
    (fun a ha b hb ↦ hcomp a (Finset.mem_toList.mp ha) b
      (Finset.mem_toList.mp hb))
    (by rw [Finset.length_toList, Finset.length_toList]; exact hle)
    (by rw [Finset.length_toList, Finset.length_toList]; exact hge)
    (Finset.nodup_toList S) (Finset.nodup_toList T) hSne.toList_ne_nil
  refine ⟨p, hch, ?_, ?_, ?_, ?_, ?_⟩
  · rw [VertPath.verts, hpl]
    ext a
    simp only [List.mem_toFinset, mem_interleave, Finset.mem_toList,
      Finset.mem_union]
  · rw [hpl, interleave_length, Finset.length_toList, Finset.length_toList]
  · intro a ha
    rw [hpl, interleave_head? hSne.toList_ne_nil] at ha
    exact Finset.mem_toList.mp (List.mem_of_mem_head? ha)
  · intro hST a ha
    rw [hpl, interleave_getLast?_eq_left (by
      rw [Finset.length_toList, Finset.length_toList]; omega)] at ha
    exact Finset.mem_toList.mp (List.mem_of_mem_getLast? ha)
  · intro hST a ha
    rw [hpl, interleave_getLast?_eq (by
      rw [Finset.length_toList, Finset.length_toList]; omega)] at ha
    exact Finset.mem_toList.mp (List.mem_of_mem_getLast? ha)

/-- If every vertex of `A` is adjacent to every vertex of `B`, then `A` can
be covered by at most `⌈|A| / (|B| + 1)⌉` alternating paths (vertices of `B`
may be reused by different paths).  Strong induction on `|A|`. -/
theorem complete_cover_aux (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ n : ℕ, ∀ A B : Finset V, A.card ≤ n → Disjoint A B →
    (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) →
    ∃ P : Finset (VertPath V),
      (∀ p ∈ P, p.toList.IsChain G.Adj) ∧
      (∀ a ∈ A, ∃ p ∈ P, a ∈ p) ∧
      P.card ≤ (A.card + B.card) / (B.card + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A B hAn hAB hadj
    rcases Finset.eq_empty_or_nonempty A with hAe | hAne
    · subst hAe
      exact ⟨∅, by simp, fun a ha ↦ by simp at ha, by simp⟩
    · have hApos := hAne.card_pos
      by_cases hsmall : A.card ≤ B.card + 1
      · -- one path covers all of `A`
        obtain ⟨U, hUB, hUcard⟩ :=
          Finset.exists_subset_card_eq (by omega : A.card - 1 ≤ B.card)
        obtain ⟨p, hch, hverts, -, -, -, -⟩ := mkAltPath_finset hAB
          (Finset.Subset.refl A) hUB
          (fun a ha b hb ↦ hadj a ha b (hUB hb))
          (by omega) (by omega) hAne
        refine ⟨{p}, ?_, ?_, ?_⟩
        · intro q hq
          rw [Finset.mem_singleton] at hq
          subst hq
          exact hch
        · intro a ha
          refine ⟨p, Finset.mem_singleton_self p, ?_⟩
          rw [← VertPath.mem_verts, hverts, Finset.mem_union]
          exact Or.inl ha
        · rw [Finset.card_singleton,
            Nat.le_div_iff_mul_le (by omega : 0 < B.card + 1)]
          omega
      · -- split off `|B| + 1` vertices of `A` and recurse
        push Not at hsmall
        obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq (le_of_lt hsmall)
        have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨p, hch, hverts, -, -, -, -⟩ := mkAltPath_finset hAB hSA
          (Finset.Subset.refl B)
          (fun a ha b hb ↦ hadj a (hSA ha) b hb)
          (by omega) (by omega) hSne
        have hlt : (A \ S).card < n := by
          rw [Finset.card_sdiff_of_subset hSA, hScard]
          omega
        obtain ⟨Q, hQch, hQcov, hQcard⟩ := ih (A \ S).card hlt (A \ S) B le_rfl
          (Disjoint.mono_left Finset.sdiff_subset hAB)
          (fun a ha b hb ↦ hadj a (Finset.mem_sdiff.mp ha).1 b hb)
        refine ⟨insert p Q, ?_, ?_, ?_⟩
        · intro q hq
          rw [Finset.mem_insert] at hq
          rcases hq with rfl | hq
          · exact hch
          · exact hQch q hq
        · intro a ha
          by_cases haS : a ∈ S
          · refine ⟨p, Finset.mem_insert_self p Q, ?_⟩
            rw [← VertPath.mem_verts, hverts, Finset.mem_union]
            exact Or.inl haS
          · have ha' : a ∈ A \ S := Finset.mem_sdiff.mpr ⟨ha, haS⟩
            obtain ⟨q, hq, hqa⟩ := hQcov a ha'
            exact ⟨q, Finset.mem_insert_of_mem hq, hqa⟩
        · have hle : (insert p Q).card ≤ Q.card + 1 :=
            Finset.card_insert_le p Q
          have hA' : (A \ S).card = A.card - (B.card + 1) := by
            rw [Finset.card_sdiff_of_subset hSA, hScard]
          rw [Nat.le_div_iff_mul_le (by omega : 0 < B.card + 1)]
          have hmul := (Nat.le_div_iff_mul_le
            (by omega : 0 < B.card + 1)).mp hQcard
          rw [hA'] at hmul
          calc (insert p Q).card * (B.card + 1) ≤ (Q.card + 1) * (B.card + 1) :=
                Nat.mul_le_mul_right _ hle
            _ = Q.card * (B.card + 1) + (B.card + 1) := by ring
            _ ≤ A.card + B.card := by omega

/-- **Lemma 2.4 (internal form).**  Stated with `fullAdj` (adjacency-based
full neighbourhoods) and `Disjoint` rather than `BipartiteOn`, so that the
induction hypothesis applies to subsets `X' ⊆ X`.  The sets `X₀, X₁, Y₀,
Y₁` are parameters with defining equations, so they stay honest atoms for
`omega`.  Strong induction on `|X|`. -/
theorem refined_aux (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ n : ℕ, ∀ (X Y X₀ X₁ Y₀ Y₁ : Finset V), X.card ≤ n →
    X₀ = fullAdj G X Y → X₁ = X \ X₀ →
    Y₀ = fullAdj G Y X → Y₁ = Y \ Y₀ →
    Disjoint X Y → Y.card < X.card → Y₀.Nonempty →
    ((X₁ = ∅ ∧ Y₁ = ∅) ∨
      ((X₀.card : ℝ) / (Y₁.card : ℝ) >
        2 * (X₁.card : ℝ) / (Y₀.card : ℝ))) →
    ∃ P : Finset (VertPath V),
      (∀ p ∈ P, p.toList.IsChain G.Adj) ∧
      (∀ v ∈ X ∪ Y, ∃ p ∈ P, v ∈ p) ∧
      P.card ≤ (X.card + Y.card) / (Y.card + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X Y X₀ X₁ Y₀ Y₁ hXn hX0d hX1d hY0d hY1d hXY hcard hY0 hcond
    -- basic facts
    have hX0sub : X₀ ⊆ X := by rw [hX0d]; exact Finset.filter_subset _ _
    have hY0sub : Y₀ ⊆ Y := by rw [hY0d]; exact Finset.filter_subset _ _
    have hX1sub : X₁ ⊆ X := by rw [hX1d]; exact Finset.sdiff_subset
    have hY1sub : Y₁ ⊆ Y := by rw [hY1d]; exact Finset.sdiff_subset
    have hY0pos : 0 < Y₀.card := hY0.card_pos
    have hYpos : 0 < Y.card := by
      have := Finset.card_le_card hY0sub
      omega
    have hX1card : X₁.card = X.card - X₀.card := by
      rw [hX1d]; exact Finset.card_sdiff_of_subset hX0sub
    have hY1card : Y₁.card = Y.card - Y₀.card := by
      rw [hY1d]; exact Finset.card_sdiff_of_subset hY0sub
    have hX0le : X₀.card ≤ X.card := Finset.card_le_card hX0sub
    have hY0le : Y₀.card ≤ Y.card := Finset.card_le_card hY0sub
    have hX1le : X₁.card ≤ X.card := Finset.card_le_card hX1sub
    have hY1le : Y₁.card ≤ Y.card := Finset.card_le_card hY1sub
    have memX0 : ∀ a : V, a ∈ X₀ ↔ a ∈ X ∧ Y ⊆ G.neighborFinset a := by
      intro a; rw [hX0d]; exact mem_fullAdj
    have memY0 : ∀ a : V, a ∈ Y₀ ↔ a ∈ Y ∧ X ⊆ G.neighborFinset a := by
      intro a; rw [hY0d]; exact mem_fullAdj
    have memX1 : ∀ a : V, a ∈ X₁ ↔ a ∈ X ∧ a ∉ X₀ := by
      intro a; rw [hX1d]; exact Finset.mem_sdiff
    have memY1 : ∀ a : V, a ∈ Y₁ ↔ a ∈ Y ∧ a ∉ Y₀ := by
      intro a; rw [hY1d]; exact Finset.mem_sdiff
    -- from (i) and (ii): `|X₀| ≥ |Y₁| + 1`
    have hX0ge : Y₁.card + 1 ≤ X₀.card := by
      rcases hcond with ⟨hXe, hYe⟩ | hratio
      · -- `X₁ = Y₁ = ∅`: then `X₀ = X` and `|X| ≥ |Y| + 1 ≥ 1`
        have hY1e : Y₁.card = 0 := by rw [hYe, Finset.card_empty]
        have hX0X : X₀ = X := Finset.Subset.antisymm hX0sub
          (Finset.sdiff_eq_empty_iff_subset.mp (hX1d ▸ hXe))
        rw [hY1e, hX0X]
        omega
      · -- the ratio hypothesis
        by_contra hlt
        push Not at hlt
        have hX0le' : X₀.card ≤ Y₁.card := by omega
        -- then `|X₁| > |Y₀| ≥ 1`
        have hX1gt : Y₀.card < X₁.card := by omega
        -- so `|Y₁| > 0` (else the LHS of the ratio is `0`)
        have hY1pos : 0 < Y₁.card := by
          by_contra hz
          push Not at hz
          have hz' : (Y₁.card : ℝ) = 0 := by
            exact_mod_cast (by omega : Y₁.card = 0)
          have hLHS : (X₀.card : ℝ) / (Y₁.card : ℝ) = 0 := by
            rw [hz', div_zero]
          rw [hLHS] at hratio
          have hge : (0:ℝ) ≤ 2 * (X₁.card : ℝ) / (Y₀.card : ℝ) := by positivity
          linarith
        have hle1 : (X₀.card : ℝ) / (Y₁.card : ℝ) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast hY1pos)]
          exact_mod_cast hX0le'
        have hgt2 : (2:ℝ) < 2 * (X₁.card : ℝ) / (Y₀.card : ℝ) := by
          have hY0r : (0:ℝ) < (Y₀.card : ℝ) := by exact_mod_cast hY0pos
          rw [lt_div_iff₀ hY0r]
          have h : (Y₀.card : ℝ) < X₁.card := by exact_mod_cast hX1gt
          linarith
        linarith
    -- the path `P`: alternates between `X₀` and `Y₁`, starts and ends in `X₀`
    obtain ⟨S, hSX0, hScard⟩ := Finset.exists_subset_card_eq hX0ge
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hch, hpverts, hplen, hphead, hplast, -⟩ := mkAltPath_finset hXY
      (hSX0.trans hX0sub) hY1sub
      (fun a ha b hb ↦ fullAdj_adj (hX0d ▸ hSX0 ha) ((memY1 b).mp hb).1)
      (by omega) (by omega) hSne
    -- the path `Q`: alternates between `Y₀` and `X ∖ V(P)`, covers
    -- `min |Y₀| |X₁|` vertices of `X₁`
    obtain ⟨T, hTX1, hTcard⟩ := Finset.exists_subset_card_eq
      (min_le_right _ _ : min Y₀.card X₁.card ≤ X₁.card)
    have hWle : Y₀.card - T.card ≤ (X₀ \ S).card := by
      rw [Finset.card_sdiff_of_subset hSX0, hScard]
      rcases le_or_gt X₁.card Y₀.card with hle | hgt
      · rw [min_eq_right hle] at hTcard
        omega
      · rw [min_eq_left (le_of_lt hgt)] at hTcard
        omega
    obtain ⟨W, hWX0S, hWcard⟩ := Finset.exists_subset_card_eq hWle
    have hWsub : W ⊆ X₀ := hWX0S.trans Finset.sdiff_subset
    have hTW : Disjoint T W := by
      rw [Finset.disjoint_left]
      intro a haT haW
      exact absurd (hWsub haW) ((memX1 a).mp (hTX1 haT)).2
    have hTWcard : (T ∪ W).card = Y₀.card := by
      rw [Finset.card_union_of_disjoint hTW, hWcard]
      have hle : T.card ≤ Y₀.card := by
        rw [hTcard]; exact min_le_left _ _
      omega
    have hTWX : T ∪ W ⊆ X :=
      Finset.union_subset (hTX1.trans hX1sub)
        (hWsub.trans hX0sub)
    obtain ⟨q, hqch, hqverts, hqlen, hqhead, -, -⟩ := mkAltPath_finset hXY.symm
      hY0sub hTWX
      (fun a ha b hb ↦ fullAdj_adj (hY0d ▸ ha) (hTWX hb))
      (by omega) (by omega) hY0
    -- `P` and `Q` are disjoint and join at `x₀ ∈ X₀`, `y₀ ∈ Y₀`
    have hpqdisj : ∀ a ∈ p.toList, a ∉ q.toList := by
      intro a ha hb
      have ha' : a ∈ p.verts := VertPath.mem_verts.mpr ha
      have hb' : a ∈ q.verts := VertPath.mem_verts.mpr hb
      rw [hpverts, Finset.mem_union] at ha'
      rw [hqverts, Finset.mem_union, Finset.mem_union] at hb'
      rcases ha' with haS | haY1
      · have haX : a ∈ X := hX0sub (hSX0 haS)
        rcases hb' with hbY0 | hbTW
        · exact Finset.disjoint_left.mp hXY haX (hY0sub hbY0)
        · rcases hbTW with hbT | hbW
          · exact absurd (hSX0 haS) ((memX1 a).mp (hTX1 hbT)).2
          · exact absurd haS (Finset.mem_sdiff.mp (hWX0S hbW)).2
      · have haY : a ∈ Y := hY1sub haY1
        rcases hb' with hbY0 | hbTW
        · exact absurd hbY0 ((memY1 a).mp haY1).2
        · exact Finset.disjoint_left.mp hXY.symm haY
            (hTWX (Finset.mem_union.mpr hbTW))
    have hedge : ∀ a ∈ p.toList.getLast?, ∀ b ∈ q.toList.head?,
        G.Adj a b := by
      intro a ha b hb
      exact fullAdj_adj (hX0d ▸ hSX0 (hplast hScard a ha))
        (hY0sub (hqhead b hb))
    obtain ⟨r, hrl, hrch⟩ := mkAppendPath hch hqch hedge hpqdisj
    -- facts about `R = P ++ Q`
    have hrverts : r.verts = p.verts ∪ q.verts := by
      simp only [VertPath.verts, hrl, List.toFinset_append]
    have hrY : ∀ y ∈ Y, y ∈ r.verts := by
      intro y hy
      rw [hrverts, Finset.mem_union]
      by_cases hy0 : y ∈ Y₀
      · exact Or.inr (by
          rw [hqverts, Finset.mem_union]; exact Or.inl hy0)
      · have hy1 : y ∈ Y₁ := (memY1 y).mpr ⟨hy, hy0⟩
        exact Or.inl (by
          rw [hpverts, Finset.mem_union]; exact Or.inr hy1)
    have hSdisjTW : Disjoint S (T ∪ W) := by
      rw [Finset.disjoint_left]
      intro a haS hb
      rw [Finset.mem_union] at hb
      rcases hb with hbT | hbW
      · exact absurd (hSX0 haS) ((memX1 a).mp (hTX1 hbT)).2
      · exact absurd haS (Finset.mem_sdiff.mp (hWX0S hbW)).2
    have hrX : r.verts ∩ X = S ∪ (T ∪ W) := by
      rw [hrverts, hpverts, hqverts]
      ext a
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨(haS | haY1) | (hbY0 | hbTW), haX⟩
        · exact Or.inl haS
        · exact absurd haX (Finset.disjoint_left.mp hXY.symm
            (hY1sub haY1))
        · exact absurd haX (Finset.disjoint_left.mp hXY.symm (hY0sub hbY0))
        · exact Or.inr hbTW
      · rintro (haS | hbTW)
        · exact ⟨Or.inl (Or.inl haS), hX0sub (hSX0 haS)⟩
        · exact ⟨Or.inr (Or.inr hbTW), hTWX (Finset.mem_union.mpr hbTW)⟩
    have hrXcard : (r.verts ∩ X).card = Y.card + 1 := by
      rw [hrX, Finset.card_union_of_disjoint hSdisjTW, hScard, hTWcard]
      omega
    have hX'card : (X \ r.verts).card = X.card - Y.card - 1 := by
      rw [Finset.card_sdiff, hrXcard]
      omega
    by_cases hX'0 : (X \ r.verts).card = 0
    · -- `|X| = |Y| + 1`: `R` alone covers `X ∪ Y`
      refine ⟨{r}, ?_, ?_, ?_⟩
      · intro t ht
        rw [Finset.mem_singleton] at ht
        subst ht
        exact hrch
      · intro v hv
        refine ⟨r, Finset.mem_singleton_self r, ?_⟩
        rw [Finset.mem_union] at hv
        rcases hv with hv | hv
        · have hXsub : X ⊆ r.verts := Finset.sdiff_eq_empty_iff_subset.mp
            (Finset.card_eq_zero.mp hX'0)
          exact VertPath.mem_verts.mp (hXsub hv)
        · exact VertPath.mem_verts.mp (hrY v hv)
      · rw [Finset.card_singleton,
          Nat.le_div_iff_mul_le (by omega : 0 < Y.card + 1)]
        omega
    · -- `|X'| > 0`: set up the partition of the induced subgraph `G'`.
      -- We write `X' = X \ V(R)`, `X₀' = fullAdj G X' Y`, etc. explicitly.
      push Not at hX'0
      have hX'sub : X \ r.verts ⊆ X := Finset.sdiff_subset
      have memX' : ∀ a : V, a ∈ X \ r.verts ↔ a ∈ X ∧ a ∉ r.verts :=
        fun a ↦ Finset.mem_sdiff
      have memX0' : ∀ a : V, a ∈ fullAdj G (X \ r.verts) Y ↔
          a ∈ X \ r.verts ∧ Y ⊆ G.neighborFinset a :=
        fun a ↦ mem_fullAdj
      have memY0' : ∀ a : V, a ∈ fullAdj G Y (X \ r.verts) ↔
          a ∈ Y ∧ X \ r.verts ⊆ G.neighborFinset a :=
        fun a ↦ mem_fullAdj
      have hX0'sub : fullAdj G (X \ r.verts) Y ⊆ X₀ := by
        intro a ha
        rw [memX0'] at ha
        rw [memX0]
        exact ⟨hX'sub ha.1, ha.2⟩
      have hY0sub' : Y₀ ⊆ fullAdj G Y (X \ r.verts) := by
        intro a ha
        rw [memY0', memY0] at *
        exact ⟨ha.1, fun b hb ↦ ha.2 (hX'sub hb)⟩
      have hY1'sub : Y \ fullAdj G Y (X \ r.verts) ⊆ Y₁ := by
        intro a ha
        rw [Finset.mem_sdiff] at ha
        rw [memY1]
        exact ⟨ha.1, fun hb ↦ ha.2 (hY0sub' hb)⟩
      have hY0'ne : (fullAdj G Y (X \ r.verts)).Nonempty :=
        hY0.mono hY0sub'
      have hX'Y : Disjoint (X \ r.verts) Y :=
        Disjoint.mono_left hX'sub hXY
      -- `X₁' = X₁ ∖ V(R)` and `X₀' = X₀ ∖ V(R)`
      have hX1'eq : (X \ r.verts) \ fullAdj G (X \ r.verts) Y =
          X₁ \ r.verts := by
        ext a
        simp only [Finset.mem_sdiff, memX0', memX1, memX0]
        constructor
        · rintro ⟨⟨haX, harv⟩, ha0'⟩
          exact ⟨⟨haX, fun hb ↦ ha0' ⟨⟨haX, harv⟩, hb.2⟩⟩, harv⟩
        · rintro ⟨⟨haX, ha0⟩, harv⟩
          exact ⟨⟨haX, harv⟩, fun hb ↦ ha0 ⟨haX, hb.2⟩⟩
      have hX0'eq : fullAdj G (X \ r.verts) Y = X₀ \ r.verts := by
        ext a
        simp only [Finset.mem_sdiff, memX0', memX0]
        constructor
        · rintro ⟨⟨haX, harv⟩, hadj⟩
          exact ⟨⟨haX, hadj⟩, harv⟩
        · rintro ⟨⟨haX, hadj⟩, harv⟩
          exact ⟨⟨haX, harv⟩, hadj⟩
      by_cases hbip' : (X \ r.verts) \ fullAdj G (X \ r.verts) Y = ∅ ∨
          Y \ fullAdj G Y (X \ r.verts) = ∅
      · -- `G'` is complete bipartite: cover `X'` directly
        have hadj : ∀ a ∈ X \ r.verts, ∀ b ∈ Y, G.Adj a b := by
          rcases hbip' with h | h
          · intro a ha b hb
            have ha0 : a ∈ fullAdj G (X \ r.verts) Y := by
              by_contra ha0
              have hmem : a ∈ (X \ r.verts) \ fullAdj G (X \ r.verts) Y :=
                Finset.mem_sdiff.mpr ⟨ha, ha0⟩
              rw [h] at hmem
              exact Finset.notMem_empty a hmem
            exact fullAdj_adj ha0 hb
          · intro a ha b hb
            have hb0 : b ∈ fullAdj G Y (X \ r.verts) := by
              by_contra hb0
              have hmem : b ∈ Y \ fullAdj G Y (X \ r.verts) :=
                Finset.mem_sdiff.mpr ⟨hb, hb0⟩
              rw [h] at hmem
              exact Finset.notMem_empty b hmem
            exact (fullAdj_adj hb0 ha).symm
        obtain ⟨Pf, hPfch, hPfcov, hPfcard⟩ :=
          complete_cover_aux G (X \ r.verts).card (X \ r.verts) Y le_rfl
            hX'Y hadj
        refine ⟨insert r Pf, ?_, ?_, ?_⟩
        · intro t ht
          rw [Finset.mem_insert] at ht
          rcases ht with rfl | ht
          · exact hrch
          · exact hPfch t ht
        · intro v hv
          rw [Finset.mem_union] at hv
          rcases hv with hv | hv
          · by_cases hvr : v ∈ r.verts
            · exact ⟨r, Finset.mem_insert_self r Pf,
                VertPath.mem_verts.mp hvr⟩
            · have hv' : v ∈ X \ r.verts := Finset.mem_sdiff.mpr ⟨hv, hvr⟩
              obtain ⟨t, ht, htv⟩ := hPfcov v hv'
              exact ⟨t, Finset.mem_insert_of_mem ht, htv⟩
          · exact ⟨r, Finset.mem_insert_self r Pf,
              VertPath.mem_verts.mp (hrY v hv)⟩
        · have hdiv : (X.card + Y.card) / (Y.card + 1) =
              ((X \ r.verts).card + Y.card) / (Y.card + 1) + 1 := by
            have h1 : X.card + Y.card =
                ((X \ r.verts).card + Y.card) + (Y.card + 1) := by omega
            rw [h1, Nat.add_div_right _ (by omega : 0 < Y.card + 1)]
          calc (insert r Pf).card ≤ Pf.card + 1 := Finset.card_insert_le r Pf
            _ ≤ ((X \ r.verts).card + Y.card) / (Y.card + 1) + 1 :=
                Nat.add_le_add_right hPfcard _
            _ = (X.card + Y.card) / (Y.card + 1) := hdiv.symm
      · -- both `X₁'` and `Y₁'` are nonempty
        push Not at hbip'
        obtain ⟨hX1'ne, hY1'ne⟩ := hbip'
        have hTr : r.verts ∩ X₁ = T := by
          rw [hrverts, hpverts, hqverts]
          ext a
          simp only [Finset.mem_inter, Finset.mem_union, memX1]
          constructor
          · rintro ⟨(haS | haY1) | (hbY0 | hbTW), ⟨haX, ha0⟩⟩
            · exact absurd (hSX0 haS) ha0
            · exact absurd haX (Finset.disjoint_left.mp hXY.symm
                (hY1sub haY1))
            · exact absurd haX (Finset.disjoint_left.mp hXY.symm
                (hY0sub hbY0))
            · rcases hbTW with hbT | hbW
              · exact hbT
              · exact absurd ((Finset.mem_sdiff.mp (hWX0S hbW)).1) ha0
          · intro haT
            exact ⟨Or.inr (Or.inr (Or.inl haT)),
              (memX1 a).mp (hTX1 haT)⟩
        -- `|X₁| > |Y₀|` (else `X₁'` would be empty)
        have hX1gt : Y₀.card < X₁.card := by
          by_contra hle
          push Not at hle
          rw [min_eq_right hle] at hTcard
          have hzero : ((X \ r.verts) \ fullAdj G (X \ r.verts) Y).card = 0 := by
            rw [hX1'eq, Finset.card_sdiff, hTr, hTcard, Nat.sub_self]
          exact absurd (Finset.card_eq_zero.mp hzero)
            (Finset.nonempty_iff_ne_empty.mp hX1'ne)
        -- so `W = ∅`, `T` has size `|Y₀|` and `hcond` is the ratio
        have hT' : T.card = Y₀.card := by
          rw [hTcard, min_eq_left (le_of_lt hX1gt)]
        have hWe : W = ∅ :=
          Finset.card_eq_zero.mp (by rw [hWcard, hT', Nat.sub_self])
        have hX0'card : (fullAdj G (X \ r.verts) Y).card =
            X₀.card - Y₁.card - 1 := by
          rw [hX0'eq]
          have hX0r : r.verts ∩ X₀ = S := by
            rw [hrverts, hpverts, hqverts]
            ext a
            simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨(haS | haY1) | (hbY0 | hbTW), haX0⟩
              · exact haS
              · exact absurd (hY1sub haY1)
                  (Finset.disjoint_left.mp hXY (hX0sub haX0))
              · exact absurd (hY0sub hbY0)
                  (Finset.disjoint_left.mp hXY (hX0sub haX0))
              · rcases hbTW with hbT | hbW
                · exact absurd hbT (fun h ↦ ((memX1 a).mp (hTX1 h)).2 haX0)
                · rw [hWe] at hbW
                  exact absurd hbW (Finset.notMem_empty a)
            · intro haS
              exact ⟨Or.inl (Or.inl haS), hSX0 haS⟩
          rw [Finset.card_sdiff, hX0r, hScard]
          omega
        have hX1'card : ((X \ r.verts) \ fullAdj G (X \ r.verts) Y).card =
            X₁.card - Y₀.card := by
          rw [hX1'eq, Finset.card_sdiff, hTr, hT']
        have hY1'le : (Y \ fullAdj G Y (X \ r.verts)).card ≤ Y₁.card :=
          Finset.card_le_card hY1'sub
        have hY0'ge : Y₀.card ≤ (fullAdj G Y (X \ r.verts)).card :=
          Finset.card_le_card hY0sub'
        have hY1'pos : 0 < (Y \ fullAdj G Y (X \ r.verts)).card :=
          hY1'ne.card_pos
        have hY0'pos : 0 < (fullAdj G Y (X \ r.verts)).card :=
          hY0'ne.card_pos
        have hY1pos : 0 < Y₁.card := by omega
        -- the ratio condition for `G'` (paper's equation (2.1))
        obtain hratio : (X₀.card : ℝ) / (Y₁.card : ℝ) >
            2 * (X₁.card : ℝ) / (Y₀.card : ℝ) := by
          rcases hcond with ⟨hXe, hYe⟩ | h
          · obtain ⟨a, ha⟩ := hY1'ne
            have haY1 : a ∈ Y₁ := hY1'sub ha
            rw [hYe] at haY1
            exact absurd haY1 (Finset.notMem_empty a)
          · exact h
        have hY0r : (0:ℝ) < Y₀.card := by exact_mod_cast hY0pos
        have hY1r : (0:ℝ) < Y₁.card := by exact_mod_cast hY1pos
        have hY0'r : (0:ℝ) < (fullAdj G Y (X \ r.verts)).card :=
          by exact_mod_cast hY0'pos
        have hY1'r : (0:ℝ) < (Y \ fullAdj G Y (X \ r.verts)).card :=
          by exact_mod_cast hY1'pos
        have hcross : 2 * (X₁.card : ℝ) * Y₁.card <
            (X₀.card : ℝ) * Y₀.card := by
          exact (div_lt_div_iff₀ hY0r hY1r).mp hratio
        have hratio' : ((fullAdj G (X \ r.verts) Y).card : ℝ) /
            ((Y \ fullAdj G Y (X \ r.verts)).card : ℝ) >
            2 * (((X \ r.verts) \ fullAdj G (X \ r.verts) Y).card : ℝ) /
            ((fullAdj G Y (X \ r.verts)).card : ℝ) := by
          rw [gt_iff_lt, div_lt_div_iff₀ hY0'r hY1'r]
          -- suffices: (X₀−Y₁−1)·Y₀' > 2·(X₁−Y₀)·Y₁'
          have hX0'r : ((fullAdj G (X \ r.verts) Y).card : ℝ) =
              (X₀.card : ℝ) - Y₁.card - 1 := by
            rw [hX0'card, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
            push_cast; ring
          have hX1'r :
              (((X \ r.verts) \ fullAdj G (X \ r.verts) Y).card : ℝ) =
              (X₁.card : ℝ) - Y₀.card := by
            rw [hX1'card, Nat.cast_sub (by omega)]
          have hY1'r2 : ((Y \ fullAdj G Y (X \ r.verts)).card : ℝ) ≤
              Y₁.card := by exact_mod_cast hY1'le
          have hY0'r2 : (Y₀.card : ℝ) ≤ (fullAdj G Y (X \ r.verts)).card :=
            by exact_mod_cast hY0'ge
          have hX0'nn : (0:ℝ) ≤ (X₀.card : ℝ) - Y₁.card - 1 := by
            have h : (Y₁.card : ℝ) + 1 ≤ X₀.card := by exact_mod_cast hX0ge
            linarith
          rw [hX0'r, hX1'r]
          have hge1 : ((X₀.card : ℝ) - Y₁.card - 1) *
              (fullAdj G Y (X \ r.verts)).card ≥
              ((X₀.card : ℝ) - Y₁.card - 1) * Y₀.card :=
            mul_le_mul_of_nonneg_left hY0'r2 hX0'nn
          have hle2 : 2 * ((X₁.card : ℝ) - Y₀.card) *
              (Y \ fullAdj G Y (X \ r.verts)).card ≤
              2 * ((X₁.card : ℝ) - Y₀.card) * Y₁.card := by
            apply mul_le_mul_of_nonneg_left hY1'r2
            have h : (0:ℝ) < (X₁.card : ℝ) - Y₀.card := by
              have hX1gtr : (Y₀.card : ℝ) < X₁.card := by
                exact_mod_cast hX1gt
              linarith
            linarith
          have key : ((X₀.card : ℝ) - Y₁.card - 1) * Y₀.card >
              2 * ((X₁.card : ℝ) - Y₀.card) * Y₁.card := by
            have hY1r1 : (1:ℝ) ≤ Y₁.card := by exact_mod_cast hY1pos
            have hY0r1 : (0:ℝ) < Y₀.card := hY0r
            nlinarith [hcross, hY0r1, hY1r1]
          linarith [hge1, hle2, key]
        by_cases hX'gt : Y.card < (X \ r.verts).card
        · -- apply the induction hypothesis to `G' = G[X' ∪ Y]`
          obtain ⟨Pf, hPfch, hPfcov, hPfcard⟩ :=
            ih (X \ r.verts).card (by omega) (X \ r.verts) Y
              (fullAdj G (X \ r.verts) Y)
              ((X \ r.verts) \ fullAdj G (X \ r.verts) Y)
              (fullAdj G Y (X \ r.verts))
              (Y \ fullAdj G Y (X \ r.verts))
              le_rfl rfl rfl rfl rfl hX'Y hX'gt hY0'ne (.inr hratio')
          refine ⟨insert r Pf, ?_, ?_, ?_⟩
          · intro t ht
            rw [Finset.mem_insert] at ht
            rcases ht with rfl | ht
            · exact hrch
            · exact hPfch t ht
          · intro v hv
            rw [Finset.mem_union] at hv
            rcases hv with hv | hv
            · by_cases hvr : v ∈ r.verts
              · exact ⟨r, Finset.mem_insert_self r Pf,
                  VertPath.mem_verts.mp hvr⟩
              · have hv' : v ∈ X \ r.verts :=
                  Finset.mem_sdiff.mpr ⟨hv, hvr⟩
                obtain ⟨t, ht, htv⟩ := hPfcov v
                  (Finset.mem_union.mpr (Or.inl hv'))
                exact ⟨t, Finset.mem_insert_of_mem ht, htv⟩
            · exact ⟨r, Finset.mem_insert_self r Pf,
                VertPath.mem_verts.mp (hrY v hv)⟩
          · have hdiv : (X.card + Y.card) / (Y.card + 1) =
                ((X \ r.verts).card + Y.card) / (Y.card + 1) + 1 := by
              have h1 : X.card + Y.card =
                  ((X \ r.verts).card + Y.card) + (Y.card + 1) := by omega
              rw [h1, Nat.add_div_right _ (by omega : 0 < Y.card + 1)]
            calc (insert r Pf).card ≤ Pf.card + 1 := Finset.card_insert_le r Pf
              _ ≤ ((X \ r.verts).card + Y.card) / (Y.card + 1) + 1 :=
                  Nat.add_le_add_right hPfcard _
              _ = (X.card + Y.card) / (Y.card + 1) := hdiv.symm
        · -- `|X'| ≤ |Y|`: build the second path `R'`
          push Not at hX'gt
          -- then `|Y₀'| > |X₁'|` (paper's argument)
          have hY0'gt :
              ((X \ r.verts) \ fullAdj G (X \ r.verts) Y).card <
                (fullAdj G Y (X \ r.verts)).card := by
            by_contra hle
            push Not at hle
            have h2 : (2:ℝ) ≤
                2 * (((X \ r.verts) \ fullAdj G (X \ r.verts) Y).card : ℝ) /
                  ((fullAdj G Y (X \ r.verts)).card : ℝ) := by
              rw [le_div_iff₀ hY0'r]
              have h : ((fullAdj G Y (X \ r.verts)).card : ℝ) ≤
                  ((X \ r.verts) \ fullAdj G (X \ r.verts) Y).card :=
                by exact_mod_cast hle
              nlinarith [h]
            have hbig : (2:ℝ) *
                (Y \ fullAdj G Y (X \ r.verts)).card <
                (fullAdj G (X \ r.verts) Y).card := by
              have := (lt_div_iff₀ hY1'r).mp (lt_of_le_of_lt h2 hratio')
              linarith [this]
            have hbig' : 2 * (Y \ fullAdj G Y (X \ r.verts)).card <
                (fullAdj G (X \ r.verts) Y).card := by exact_mod_cast hbig
            have hsubX' : fullAdj G (X \ r.verts) Y ⊆ X \ r.verts :=
              Finset.filter_subset _ _
            have hsubY' : fullAdj G Y (X \ r.verts) ⊆ Y :=
              Finset.filter_subset _ _
            have hX'c : (X \ r.verts).card =
                (fullAdj G (X \ r.verts) Y).card +
                  ((X \ r.verts) \ fullAdj G (X \ r.verts) Y).card := by
              have h := Finset.card_sdiff_of_subset hsubX'
              have hle := Finset.card_le_card hsubX'
              omega
            have hYc : Y.card =
                (fullAdj G Y (X \ r.verts)).card +
                  (Y \ fullAdj G Y (X \ r.verts)).card := by
              have h := Finset.card_sdiff_of_subset hsubY'
              have hle := Finset.card_le_card hsubY'
              omega
            omega
          -- `Q'`: alternating path through `X₁'`, starting/ending in `Y₀'`
          obtain ⟨T', hT'Y0', hT'card⟩ := Finset.exists_subset_card_eq hY0'gt
          have hT'Y : T' ⊆ Y := hT'Y0'.trans (Finset.filter_subset _ _)
          have hT'ne : T'.Nonempty := Finset.card_pos.mp
            (by have := hX1'ne.card_pos; omega)
          obtain ⟨q', hq'ch, hq'verts, hq'len, hq'head, hq'last, -⟩ :=
            mkAltPath_finset hX'Y.symm hT'Y
              (Finset.sdiff_subset : (X \ r.verts) \ fullAdj G (X \ r.verts) Y
                ⊆ X \ r.verts)
              (fun a ha b hb ↦ fullAdj_adj (hT'Y0' ha)
                (Finset.mem_sdiff.mp hb).1)
              (by omega) (by omega) hT'ne
          have hq'X : q'.verts ∩ (X \ r.verts) =
              (X \ r.verts) \ fullAdj G (X \ r.verts) Y := by
            rw [hq'verts]
            ext a
            simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨(haT | haX), haX'⟩
              · exact absurd (hT'Y haT)
                  (Finset.disjoint_left.mp hX'Y haX')
              · exact haX
            · intro haX
              exact ⟨Or.inr haX, (Finset.mem_sdiff.mp haX).1⟩
          have hbound : ({r} ∪ {q'} : Finset (VertPath V)).card ≤
              (X.card + Y.card) / (Y.card + 1) := by
            have h2 : 2 ≤ (X.card + Y.card) / (Y.card + 1) := by
              rw [Nat.le_div_iff_mul_le (by omega : 0 < Y.card + 1)]
              omega
            calc ({r} ∪ {q'} : Finset _).card ≤ ({r} : Finset _).card +
                  ({q'} : Finset _).card := Finset.card_union_le _ _
              _ = 2 := by simp
              _ ≤ _ := h2
          by_cases hX0'e : fullAdj G (X \ r.verts) Y = ∅
          · -- `X' = X₁' ⊆ V(Q')`: `{R, Q'}` covers everything
            refine ⟨{r, q'}, ?_, ?_, ?_⟩
            · intro t ht
              rw [Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with rfl | rfl
              · exact hrch
              · exact hq'ch
            · intro v hv
              rw [Finset.mem_union] at hv
              rcases hv with hv | hv
              · by_cases hvr : v ∈ r.verts
                · exact ⟨r, Finset.mem_insert_self _ _,
                    VertPath.mem_verts.mp hvr⟩
                · have hv' : v ∈ X \ r.verts :=
                    Finset.mem_sdiff.mpr ⟨hv, hvr⟩
                  have hv1 : v ∈ (X \ r.verts) \ fullAdj G (X \ r.verts) Y := by
                    have : v ∉ fullAdj G (X \ r.verts) Y := by
                      rw [hX0'e]; exact Finset.notMem_empty v
                    exact Finset.mem_sdiff.mpr ⟨hv', this⟩
                  have : v ∈ q'.verts := by
                    have := hq'X
                    rw [Finset.ext_iff] at this
                    exact (Finset.mem_inter.mp ((this v).mpr hv1)).1
                  exact ⟨q', Finset.mem_insert_of_mem
                    (Finset.mem_singleton_self _), VertPath.mem_verts.mp this⟩
              · exact ⟨r, Finset.mem_insert_self _ _,
                  VertPath.mem_verts.mp (hrY v hv)⟩
            · have heq : ({r, q'} : Finset (VertPath V)) = {r} ∪ {q'} := by
                ext t; simp
              rw [heq]
              exact hbound
          · -- build `P'` covering `X₀'`, then `R' = Q' ++ P'`
            have hX0'ne : (fullAdj G (X \ r.verts) Y).Nonempty :=
              Finset.nonempty_iff_ne_empty.mpr hX0'e
            have hYq' : (Y \ q'.verts).card =
                Y.card - (((X \ r.verts) \ fullAdj G (X \ r.verts) Y).card + 1) := by
              have hq'Y : q'.verts ∩ Y = T' := by
                rw [hq'verts]
                ext a
                simp only [Finset.mem_inter, Finset.mem_union]
                constructor
                · rintro ⟨(haT | haX), haY⟩
                  · exact haT
                  · exact absurd haY (Finset.disjoint_left.mp hXY
                      (hX'sub (Finset.mem_sdiff.mp haX).1))
                · intro haT
                  exact ⟨Or.inl haT, hT'Y haT⟩
              rw [Finset.card_sdiff, hq'Y, hT'card]
            have hUle : (fullAdj G (X \ r.verts) Y).card - 1 ≤
                (Y \ q'.verts).card := by
              rw [hYq']
              have hX'c : (X \ r.verts).card =
                  (fullAdj G (X \ r.verts) Y).card +
                    ((X \ r.verts) \ fullAdj G (X \ r.verts) Y).card := by
                have hsubX' : fullAdj G (X \ r.verts) Y ⊆ X \ r.verts :=
                  Finset.filter_subset _ _
                have h := Finset.card_sdiff_of_subset hsubX'
                have hle := Finset.card_le_card hsubX'
                omega
              omega
            obtain ⟨U, hUY, hUcard⟩ := Finset.exists_subset_card_eq hUle
            have hUY' : U ⊆ Y := hUY.trans Finset.sdiff_subset
            have hX0'pos := hX0'ne.card_pos
            have hS' : fullAdj G (X \ r.verts) Y ⊆ X \ r.verts :=
              Finset.filter_subset _ _
            obtain ⟨p', hp'ch, hp'verts, hp'len, hp'head, -, -⟩ :=
              mkAltPath_finset hX'Y hS' hUY'
                (fun a ha b hb ↦ fullAdj_adj ha (hUY' hb))
                (by omega) (by omega) hX0'ne
            have hq'p'disj : ∀ a ∈ q'.toList, a ∉ p'.toList := by
              intro a ha hb
              have ha' : a ∈ q'.verts := VertPath.mem_verts.mpr ha
              have hb' : a ∈ p'.verts := VertPath.mem_verts.mpr hb
              rw [hq'verts, Finset.mem_union] at ha'
              rw [hp'verts, Finset.mem_union] at hb'
              rcases ha' with haT | haX
              · have haY : a ∈ Y := hT'Y haT
                rcases hb' with hbX | hbU
                · exact absurd haY (Finset.disjoint_left.mp hX'Y
                    (Finset.filter_subset _ _ hbX))
                · exact absurd (VertPath.mem_verts.mpr ha)
                    (Finset.mem_sdiff.mp (hUY hbU)).2
              · have haX' : a ∈ X \ r.verts := (Finset.mem_sdiff.mp haX).1
                rcases hb' with hbX | hbU
                · exact absurd hbX (Finset.mem_sdiff.mp haX).2
                · exact absurd (hUY' hbU)
                    (Finset.disjoint_left.mp hX'Y haX')
            have hedge' : ∀ a ∈ q'.toList.getLast?,
                ∀ b ∈ p'.toList.head?, G.Adj a b := by
              intro a ha b hb
              exact fullAdj_adj (hT'Y0' (hq'last hT'card a ha))
                ((mem_fullAdj.mp (hp'head b hb)).1)
            obtain ⟨r', hr'l, hr'ch⟩ := mkAppendPath hq'ch hp'ch hedge'
              hq'p'disj
            have hr'verts : r'.verts = q'.verts ∪ p'.verts := by
              simp only [VertPath.verts, hr'l, List.toFinset_append]
            have hX'cov : X \ r.verts ⊆ r'.verts := by
              intro a ha
              rw [hr'verts, hq'verts, hp'verts]
              by_cases ha0 : a ∈ fullAdj G (X \ r.verts) Y
              · exact Finset.mem_union.mpr
                  (Or.inr (Finset.mem_union.mpr (Or.inl ha0)))
              · have ha1 : a ∈ (X \ r.verts) \ fullAdj G (X \ r.verts) Y :=
                  Finset.mem_sdiff.mpr ⟨ha, ha0⟩
                exact Finset.mem_union.mpr
                  (Or.inl (Finset.mem_union.mpr (Or.inr ha1)))
            refine ⟨{r, r'}, ?_, ?_, ?_⟩
            · intro t ht
              rw [Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with rfl | rfl
              · exact hrch
              · exact hr'ch
            · intro v hv
              rw [Finset.mem_union] at hv
              rcases hv with hv | hv
              · by_cases hvr : v ∈ r.verts
                · exact ⟨r, Finset.mem_insert_self _ _,
                    VertPath.mem_verts.mp hvr⟩
                · have hv' : v ∈ X \ r.verts :=
                    Finset.mem_sdiff.mpr ⟨hv, hvr⟩
                  exact ⟨r', Finset.mem_insert_of_mem
                    (Finset.mem_singleton_self _),
                    VertPath.mem_verts.mp (hX'cov hv')⟩
              · exact ⟨r, Finset.mem_insert_self _ _,
                  VertPath.mem_verts.mp (hrY v hv)⟩
            · have heq : ({r, r'} : Finset (VertPath V)) = {r} ∪ {r'} := by
                ext t; simp
              rw [heq]
              have h2 : 2 ≤ (X.card + Y.card) / (Y.card + 1) := by
                rw [Nat.le_div_iff_mul_le (by omega : 0 < Y.card + 1)]
                omega
              calc ({r} ∪ {r'} : Finset _).card ≤
                    ({r} : Finset _).card + ({r'} : Finset _).card :=
                    Finset.card_union_le _ _
                _ = 2 := by simp
                _ ≤ _ := h2

end bip_cover

/-- **PVW24 Lemma 2.2.**  If every vertex of `Y` has degree at least
`(|X| + |Y|)/2` in the bipartite graph `G`, then `G` contains a path covering
all of `Y`, with `2|Y|` vertices.

(Requires `Y.Nonempty`: for `Y = ∅` a `VertPath` — which is always nonempty —
of length `2·|Y| = 0` cannot exist, while the hypotheses are still
satisfiable.) -/
theorem path_cover_two_mul (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (hbip : BipartiteOn G X Y) (hY : Y.Nonempty)
    (hdeg : ∀ y ∈ Y, 2 * (G.neighborFinset y).card ≥ X.card + Y.card) :
    ∃ p : VertPath V, p.toList.IsChain G.Adj ∧
      (∀ v ∈ p.toList, v ∈ X ∪ Y) ∧ (∀ y ∈ Y, y ∈ p) ∧
      p.toList.length = 2 * Y.card := by
  refine bip_cover.path_cover_aux hbip.1 hY fun y hy ↦ ?_
  rw [Finset.inter_eq_left.mpr (bip_cover.nbr_subset_X hbip hy)]
  exact hdeg y hy

/-- **PVW24 Lemma 2.3.**  If `|X| ≥ |Y| + 2m` and every `y ∈ Y` has degree at
least `|X| − m`, then at most `⌊|X|/|Y|⌋` paths cover all of `Y` and all but
`|Y| + 2m` vertices of `X`. -/
theorem few_paths_of_min_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (m : ℕ) (hbip : BipartiteOn G X Y)
    (hY : 0 < Y.card)
    (hcard : Y.card + 2 * m ≤ X.card)
    (hdeg : ∀ y ∈ Y, (G.neighborFinset y).card ≥ X.card - m) :
    ∃ P : Finset (VertPath V),
      (∀ p ∈ P, p.toList.IsChain G.Adj) ∧
      (∀ p ∈ P, ∀ v ∈ p.toList, v ∈ X ∪ Y) ∧
      (∀ y ∈ Y, ∃ p ∈ P, y ∈ p) ∧
      P.card ≤ X.card / Y.card ∧
      (X \ P.biUnion VertPath.verts).card ≤ Y.card + 2 * m := by
  refine bip_cover.few_paths_aux G X.card X Y m le_rfl hbip.1 hY hcard ?_
  intro y hy
  rw [Finset.inter_eq_left.mpr (bip_cover.nbr_subset_X hbip hy)]
  exact hdeg y hy

/-- **PVW24 Lemma 2.4.**  Refined covering lemma: with
`X₀ = {x ∈ X : d(x) = |Y|}`, `X₁ = X ∖ X₀`, `Y₀ = {y ∈ Y : d(y) = |X|} ≠ ∅`,
`Y₁ = Y ∖ Y₀`, if `|X| > |Y|` and either `X₁ = Y₁ = ∅` or
`|X₀|/|Y₁| > 2|X₁|/|Y₀|`, then `⌈|X|/(|Y|+1)⌉` paths cover all of `X ∪ Y`. -/
theorem refined_path_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (hbip : BipartiteOn G X Y)
    (hcard : Y.card < X.card)
    (hY0 : (fullNbr G Y X).Nonempty)
    (hcond : (X \ fullNbr G X Y = ∅ ∧ Y \ fullNbr G Y X = ∅) ∨
      ((fullNbr G X Y).card : ℝ) / ((Y \ fullNbr G Y X).card : ℝ) >
        2 * ((X \ fullNbr G X Y).card : ℝ) / ((fullNbr G Y X).card : ℝ)) :
    ∃ P : Finset (VertPath V),
      (∀ p ∈ P, p.toList.IsChain G.Adj) ∧
      (∀ v ∈ X ∪ Y, ∃ p ∈ P, v ∈ p) ∧
      P.card ≤ (X.card + Y.card) / (Y.card + 1) := by
  obtain ⟨hX0e, hY0e⟩ := bip_cover.fullNbr_eq_fullAdj hbip
  refine bip_cover.refined_aux G X.card X Y
    (bip_cover.fullAdj G X Y) (X \ bip_cover.fullAdj G X Y)
    (bip_cover.fullAdj G Y X) (Y \ bip_cover.fullAdj G Y X)
    le_rfl rfl rfl rfl rfl hbip.1 hcard ?_ ?_
  · rwa [hY0e] at hY0
  · rwa [hX0e, hY0e] at hcond

end JSP415
