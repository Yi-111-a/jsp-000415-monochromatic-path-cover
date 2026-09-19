import JSP415.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Bipartite lemmas (PVW24 Section 2)

Lemmas 2.1–2.4 of Pokrovskiy–Versteegen–Williams.  A "bipartite graph on
`X ∪ Y`" is a `SimpleGraph V` all of whose edges cross `X`–`Y`; in the
red–blue setting, blue adjacency across the bipartition means non-`G`-adjacent
pairs `(x, y)` with `x ∈ X, y ∈ Y` (in either order).
-/

open Finset

namespace JSP415

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both endpoints lie in the bipartition, on opposite sides. -/
def acrossXY (X Y : Finset V) (a b : V) : Prop :=
  (a ∈ X ∧ b ∈ Y) ∨ (a ∈ Y ∧ b ∈ X)

/-- Colour-`c` adjacency restricted to the bipartition `X Y`: an edge of the
(complete) bipartite graph coloured `c`. -/
def Color.adjXY (G : SimpleGraph V) (X Y : Finset V) : Color → V → V → Prop
  | .red, a, b => acrossXY X Y a b ∧ G.Adj a b
  | .blue, a, b => acrossXY X Y a b ∧ ¬G.Adj a b

/-- `G` is a bipartite graph with parts `X`, `Y`: every edge crosses. -/
def BipartiteOn (G : SimpleGraph V) (X Y : Finset V) : Prop :=
  Disjoint X Y ∧ ∀ a b : V, G.Adj a b → acrossXY X Y a b

/-- Vertices of one part adjacent to *all* vertices of the other part
(the `X₀`/`Y₀` of Lemma 2.4). -/
def fullNbr (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : Finset V :=
  X.filter fun x ↦ (G.neighborFinset x).card = Y.card

namespace bip_ramsey_path

variable {G : SimpleGraph V} {X Y : Finset V}

theorem Disjoint.notMem_left {a : V} (hXY : Disjoint X Y) (ha : a ∈ X) : a ∉ Y :=
  Finset.disjoint_left.mp hXY ha

theorem Disjoint.notMem_right {a : V} (hXY : Disjoint X Y) (ha : a ∈ Y) : a ∉ X :=
  Finset.disjoint_left.mp hXY.symm ha

theorem acrossXY.symm {a b : V} (h : acrossXY X Y a b) : acrossXY X Y b a :=
  h.elim (fun h ↦ .inr ⟨h.2, h.1⟩) (fun h ↦ .inl ⟨h.2, h.1⟩)

theorem Color.adjXY.symm {c : Color} {a b : V} (h : Color.adjXY G X Y c a b) :
    Color.adjXY G X Y c b a := by
  cases c with
  | red => exact ⟨acrossXY.symm h.1, h.2.symm⟩
  | blue => exact ⟨acrossXY.symm h.1, fun hba ↦ h.2 hba.symm⟩

theorem Color.adjXY_cases {a b : V} (h : acrossXY X Y a b) :
    Color.adjXY G X Y .red a b ∨ Color.adjXY G X Y .blue a b := by
  by_cases hadj : G.Adj a b
  · exact Or.inl ⟨h, hadj⟩
  · exact Or.inr ⟨h, hadj⟩

theorem acrossXY.left_mem {a b : V} (h : acrossXY X Y a b) : a ∈ X ∨ a ∈ Y :=
  h.elim (fun h ↦ .inl h.1) (fun h ↦ .inr h.1)

theorem acrossXY.right_mem {a b : V} (h : acrossXY X Y a b) : b ∈ X ∨ b ∈ Y :=
  acrossXY.left_mem (acrossXY.symm h)

theorem acrossXY.left_mem_iff {a b : V} (hXY : Disjoint X Y) (h : acrossXY X Y a b) :
    a ∈ X ↔ b ∈ Y := by
  obtain h | h := h
  · exact ⟨fun _ ↦ h.2, fun _ ↦ h.1⟩
  · exact ⟨fun ha ↦ absurd h.1 (Disjoint.notMem_left hXY ha),
           fun hb ↦ absurd h.2 (Disjoint.notMem_right hXY hb)⟩

theorem Color.adjXY.across {c : Color} {a b : V} (h : Color.adjXY G X Y c a b) :
    acrossXY X Y a b := by
  cases c <;> exact h.1

theorem Color.adjXY.left_mem_iff {c : Color} {a b : V} (hXY : Disjoint X Y)
    (h : Color.adjXY G X Y c a b) : a ∈ X ↔ b ∈ Y :=
  acrossXY.left_mem_iff hXY (Color.adjXY.across h)

theorem Color.adjXY.right_mem_iff {c : Color} {a b : V} (hXY : Disjoint X Y)
    (h : Color.adjXY G X Y c a b) : a ∈ Y ↔ b ∈ X := by
  obtain h' | h' := Color.adjXY.across h
  · exact ⟨fun ha ↦ absurd h'.1 (Disjoint.notMem_right hXY ha),
           fun hb ↦ absurd h'.2 (Disjoint.notMem_left hXY hb)⟩
  · exact ⟨fun _ ↦ h'.2, fun _ ↦ h'.1⟩

/-- In a chain over `adjXY`, consecutive vertices lie on opposite sides:
`l[i] ∈ X ↔ l[i+1] ∈ Y` and `l[i] ∈ Y ↔ l[i+1] ∈ X`. -/
theorem Color.adjXY.next_mem_iff {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y) {i : ℕ}
    (hi : i + 1 < l.length) :
    (l[i] ∈ X ↔ l[i+1] ∈ Y) ∧ (l[i] ∈ Y ↔ l[i+1] ∈ X) := by
  have hedge : Color.adjXY G X Y c l[i] l[i+1] := by
    rw [List.isChain_iff_getElem] at h
    exact h i hi
  exact ⟨Color.adjXY.left_mem_iff hXY hedge, Color.adjXY.right_mem_iff hXY hedge⟩

/-- Vertices two steps apart in a chain lie on the same side. -/
theorem Color.adjXY.mem_of_two {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y) {i : ℕ}
    (hi : i + 2 < l.length) : (l[i] ∈ X ↔ l[i+2] ∈ X) ∧ (l[i] ∈ Y ↔ l[i+2] ∈ Y) := by
  have h1 := Color.adjXY.next_mem_iff h hXY (i := i) (by omega)
  have h2 := Color.adjXY.next_mem_iff h hXY (i := i + 1) (by omega)
  exact ⟨h1.1.trans h2.2, h1.2.trans h2.1⟩

/-- Vertices an even number of steps apart in a chain lie on the same side. -/
theorem Color.adjXY.mem_of_even_dist {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y) {i t : ℕ}
    (hi : i + 2 * t < l.length) :
    (l[i] ∈ X ↔ l[i + 2 * t] ∈ X) ∧ (l[i] ∈ Y ↔ l[i + 2 * t] ∈ Y) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hi' : i + 2 * t < l.length := by omega
    obtain ⟨hx, hy⟩ := ih hi'
    have h2 := Color.adjXY.mem_of_two h hXY (i := i + 2 * t) (by omega)
    show (l[i] ∈ X ↔ l[i + 2 * t + 2] ∈ X) ∧ (l[i] ∈ Y ↔ l[i + 2 * t + 2] ∈ Y)
    exact ⟨hx.trans h2.1, hy.trans h2.2⟩

/-- Two vertices of a chain at positions `i ≤ j` of the same parity lie on the
same side. -/
theorem Color.adjXY.same_side {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) (hpar : (j - i) % 2 = 0) :
    (l[i] ∈ X ↔ l[j] ∈ X) ∧ (l[i] ∈ Y ↔ l[j] ∈ Y) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, j = i + 2 * t := ⟨(j - i) / 2, by omega⟩
  subst ht
  have hlen : i + 2 * t < l.length := hj
  exact Color.adjXY.mem_of_even_dist h hXY hlen

/-- Two vertices of a chain at positions `i ≤ j` of opposite parity lie on
opposite sides. -/
theorem Color.adjXY.opp_side {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) (hpar : (j - i) % 2 = 1) :
    (l[i] ∈ X ↔ l[j] ∈ Y) ∧ (l[i] ∈ Y ↔ l[j] ∈ X) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, j = i + 2 * t + 1 := ⟨(j - i - 1) / 2, by omega⟩
  subst ht
  have h1 := Color.adjXY.mem_of_even_dist h hXY (i := i) (t := t) (by omega)
  have h2 := Color.adjXY.next_mem_iff h hXY (i := i + 2 * t) (by omega)
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem Color.adjXY.isChain_reverse {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) : l.reverse.IsChain (Color.adjXY G X Y c) := by
  rw [List.isChain_reverse]
  exact h.imp (fun _ _ ↦ Color.adjXY.symm)

/-- A *bipath* `(A, z, B)` is a list `A ++ z :: B` of distinct vertices such
that `A ++ [z]` is a red chain and `z :: B` is a blue chain.  `z` is the
*midpoint*.  (Gyárfás–Lehel's `S = (A₁,…,Aᵣ,X,B₁,…,Bₛ)`.) -/
def IsBipath (G : SimpleGraph V) (X Y : Finset V) (A : List V) (z : V) (B : List V) : Prop :=
  (A ++ [z]).IsChain (Color.adjXY G X Y .red) ∧
  (z :: B).IsChain (Color.adjXY G X Y .blue) ∧
  (A ++ z :: B).Nodup

/-- Number of vertices of the bipath. -/
def bipathLen (A : List V) (z : V) (B : List V) : ℕ := A.length + B.length + 1

/-- Existence of a bipath of maximum length. -/
theorem exists_max_bipath (G : SimpleGraph V) (X Y : Finset V) (v : V) :
    ∃ A z B, IsBipath G X Y A z B ∧
      ∀ A' z' B', IsBipath G X Y A' z' B' → bipathLen A' z' B' ≤ bipathLen A z B := by
  classical
  have : Nonempty V := ⟨v⟩
  have hPM := Nat.findGreatest_spec
    (P := fun m ↦ ∃ A z B, IsBipath G X Y A z B ∧ bipathLen A z B = m)
    (n := Fintype.card V) Fintype.card_pos
    (m := 1) ⟨[], v, [], ⟨List.isChain_singleton v, List.isChain_singleton v, by simp⟩,
              by simp [bipathLen]⟩
  obtain ⟨A, z, B, hb, hlen⟩ := hPM
  refine ⟨A, z, B, hb, fun A' z' B' hb' ↦ ?_⟩
  have hle : bipathLen A' z' B' ≤ Fintype.card V := by
    have hnd : (A' ++ z' :: B').Nodup := hb'.2.2
    have := hnd.length_le_card
    simp only [bipathLen, List.length_append, List.length_cons] at this ⊢
    omega
  have hle' : bipathLen A' z' B' ≤ Nat.findGreatest
      (fun m ↦ ∃ A z B, IsBipath G X Y A z B ∧ bipathLen A z B = m)
      (Fintype.card V) :=
    Nat.le_findGreatest hle ⟨A', z', B', hb', rfl⟩
  omega

/-!
### Path / component infrastructure

Rather than using `SimpleGraph.Walk`, we work directly with vertex lists
(`List.IsChain`), matching the `VertPath` representation.  `Reach r u v`
means a chain of `r`-edges runs from `u` to `v`; `ReachIn r S` restricts the
chain to a set `S`; `compOf r S v` is the connected component of `v` inside
`S`.
-/

variable (r : V → V → Prop)

/-- A list path from `u` to `v`. -/
def Reach (u v : V) : Prop :=
  ∃ l : List V, l.IsChain r ∧ l.head? = some u ∧ l.getLast? = some v

/-- A list path from `u` to `v` staying inside `S`. -/
def ReachIn (S : Finset V) (u v : V) : Prop :=
  ∃ l : List V, l.IsChain r ∧ (∀ x ∈ l, x ∈ S) ∧ l.head? = some u ∧ l.getLast? = some v

theorem Reach.refl (u : V) : Reach r u u :=
  ⟨[u], List.isChain_singleton u, rfl, rfl⟩

theorem Reach.symm (hrs : ∀ a b, r a b → r b a) {u v : V} (h : Reach r u v) :
    Reach r v u := by
  obtain ⟨l, hl, hh, ht⟩ := h
  refine ⟨l.reverse, ?_, ?_, ?_⟩
  · rw [List.isChain_reverse]
    exact hl.imp fun _ _ ↦ hrs _ _
  · rwa [List.head?_reverse]
  · rwa [List.getLast?_reverse]

theorem Reach.trans {u v w : V} (h1 : Reach r u v) (h2 : Reach r v w) :
    Reach r u w := by
  obtain ⟨l1, h1c, h1h, h1t⟩ := h1
  obtain ⟨l2, h2c, h2h, h2t⟩ := h2
  cases l2 with
  | nil => simp at h2h
  | cons b t =>
    simp only [List.head?_cons, Option.some_inj] at h2h
    subst h2h
    have hl1ne : l1 ≠ [] := fun h ↦ by subst h; simp at h1h
    have hl1last : l1.getLast hl1ne = b := by
      rw [← Option.some_inj, ← List.getLast?_eq_getLast_of_ne_nil hl1ne]
      exact h1t
    refine ⟨l1 ++ t, ?_, ?_, ?_⟩
    · rw [List.isChain_append]
      refine ⟨h1c, h2c.tail, fun x hx y hy ↦ ?_⟩
      rw [List.getLast?_eq_getLast_of_ne_nil hl1ne, Option.mem_some_iff] at hx
      subst x
      rw [hl1last]
      exact (List.isChain_cons.mp h2c).1 _ hy
    · rw [List.head?_append_of_ne_nil _ hl1ne]; exact h1h
    · cases t with
      | nil =>
        simp only [List.append_nil, List.getLast?_singleton, Option.some_inj] at h2t ⊢
        rwa [← h2t]
      | cons c t' =>
        have hstep : (b :: c :: t').getLast? = (c :: t').getLast? := by
          simp [List.getLast?_cons]
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _), ← hstep]
        exact h2t

theorem Reach.in {u v : V} (h : Reach r u v) : ReachIn r Finset.univ u v := by
  obtain ⟨l, hl, hh, ht⟩ := h
  exact ⟨l, hl, fun _ _ ↦ Finset.mem_univ _, hh, ht⟩

theorem ReachIn.reach {S : Finset V} {u v : V} (h : ReachIn r S u v) : Reach r u v := by
  obtain ⟨l, hl, -, hh, ht⟩ := h
  exact ⟨l, hl, hh, ht⟩

theorem ReachIn.refl {S : Finset V} {u : V} (hu : u ∈ S) : ReachIn r S u u :=
  ⟨[u], List.isChain_singleton u, fun x hx ↦ by simpa using (List.mem_singleton.mp hx ▸ hu),
    rfl, rfl⟩

theorem ReachIn.symm (hrs : ∀ a b, r a b → r b a) {S : Finset V} {u v : V}
    (h : ReachIn r S u v) : ReachIn r S v u := by
  obtain ⟨l, hl, hS, hh, ht⟩ := h
  refine ⟨l.reverse, ?_, ?_, ?_, ?_⟩
  · rw [List.isChain_reverse]
    exact hl.imp fun _ _ ↦ hrs _ _
  · intro x hx; exact hS _ (List.mem_reverse.mp hx)
  · rwa [List.head?_reverse]
  · rwa [List.getLast?_reverse]

theorem ReachIn.trans {S : Finset V} {u v w : V} (h1 : ReachIn r S u v)
    (h2 : ReachIn r S v w) : ReachIn r S u w := by
  obtain ⟨l1, h1c, h1S, h1h, h1t⟩ := h1
  obtain ⟨l2, h2c, h2S, h2h, h2t⟩ := h2
  cases l2 with
  | nil => simp at h2h
  | cons b t =>
    simp only [List.head?_cons, Option.some_inj] at h2h
    subst h2h
    have hl1ne : l1 ≠ [] := fun h ↦ by subst h; simp at h1h
    have hl1last : l1.getLast hl1ne = b := by
      rw [← Option.some_inj, ← List.getLast?_eq_getLast_of_ne_nil hl1ne]
      exact h1t
    refine ⟨l1 ++ t, ?_, ?_, ?_, ?_⟩
    · rw [List.isChain_append]
      refine ⟨h1c, h2c.tail, fun x hx y hy ↦ ?_⟩
      rw [List.getLast?_eq_getLast_of_ne_nil hl1ne, Option.mem_some_iff] at hx
      subst x
      rw [hl1last]
      exact (List.isChain_cons.mp h2c).1 _ hy
    · intro x hx
      rw [List.mem_append] at hx
      exact hx.elim (h1S _) fun hx ↦ h2S _ (List.mem_cons_of_mem _ hx)
    · rw [List.head?_append_of_ne_nil _ hl1ne]; exact h1h
    · cases t with
      | nil =>
        simp only [List.append_nil, List.getLast?_singleton, Option.some_inj] at h2t ⊢
        rwa [← h2t]
      | cons c t' =>
        have hstep : (b :: c :: t').getLast? = (c :: t').getLast? := by
          simp [List.getLast?_cons]
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _), ← hstep]
        exact h2t

theorem ReachIn.mem_left {S : Finset V} {u v : V} (h : ReachIn r S u v) : u ∈ S := by
  obtain ⟨l, -, hS, hh, -⟩ := h
  cases l with
  | nil => simp at hh
  | cons a t =>
    simp only [List.head?_cons, Option.some_inj] at hh
    subst hh
    exact hS _ List.mem_cons_self

theorem ReachIn.mem_right {S : Finset V} {u v : V} (h : ReachIn r S u v) : v ∈ S := by
  obtain ⟨l, -, hS, -, ht⟩ := h
  have hne : l ≠ [] := fun h' ↦ by subst h'; simp at ht
  have htv : l.getLast hne = v := by
    rw [← Option.some_inj, ← List.getLast?_eq_getLast_of_ne_nil hne]
    exact ht
  subst htv
  exact hS _ (List.getLast_mem hne)

/-- The connected component of `v` inside `S`. -/
noncomputable def compOf (S : Finset V) (v : V) : Finset V :=
  letI := Classical.decPred fun w ↦ ReachIn r S v w
  S.filter fun w ↦ ReachIn r S v w

variable {r}

theorem mem_compOf {S : Finset V} {u v : V} : v ∈ compOf r S u ↔ ReachIn r S u v := by
  classical
  rw [compOf, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨ReachIn.mem_right r h, h⟩⟩

theorem compOf_subset {S : Finset V} {v : V} : compOf r S v ⊆ S := by
  classical
  rw [compOf]
  exact Finset.filter_subset _ _

theorem mem_compOf_self {S : Finset V} {v : V} (hv : v ∈ S) : v ∈ compOf r S v :=
  mem_compOf.mpr (ReachIn.refl r hv)

theorem ReachIn.compOf_eq {S : Finset V} {u v : V} (hrs : ∀ a b, r a b → r b a)
    (h : ReachIn r S u v) : compOf r S u = compOf r S v := by
  ext w
  rw [mem_compOf, mem_compOf]
  exact ⟨fun hw ↦ ReachIn.trans r (ReachIn.symm r hrs h) hw,
    fun hw ↦ ReachIn.trans r h hw⟩

theorem compOf_eq_of_mem {S : Finset V} {u v : V} (hrs : ∀ a b, r a b → r b a)
    (h : v ∈ compOf r S u) : compOf r S u = compOf r S v :=
  ReachIn.compOf_eq hrs (mem_compOf.mp h)

/-- No edge leaves a component: if `v` reaches `u` inside `S`, `w ∈ S` and
`r v w` then `w` also reaches `u` inside `S`. -/
theorem ReachIn.of_adj {S : Finset V} {u v w : V} (h : ReachIn r S u v)
    (hw : w ∈ S) (hrw : r v w) : ReachIn r S u w := by
  obtain ⟨l, hl, hS, hh, ht⟩ := h
  have hlne : l ≠ [] := fun h' ↦ by subst h'; simp at hh
  have hlv : l.getLast hlne = v := by
    rw [← Option.some_inj]; rwa [← List.getLast?_eq_getLast_of_ne_nil]
  refine ⟨l ++ [w], ?_, ?_, ?_, ?_⟩
  · rw [List.isChain_append]
    refine ⟨hl, List.isChain_singleton w, fun x hx y hy ↦ ?_⟩
    simp only [List.getLast?_eq_getLast_of_ne_nil hlne, List.head?_cons,
      Option.mem_some_iff] at hx hy
    subst x; subst y
    rwa [hlv]
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hS _ hx
    · rw [List.mem_singleton] at hx; subst hx; exact hw
  · rw [List.head?_append_of_ne_nil _ hlne]; exact hh
  · simp

/-- No edge leaves a component. -/
theorem mem_compOf_of_adj {S : Finset V} {u v w : V} (h : ReachIn r S u v)
    (hw : w ∈ S) (hrw : r v w) : w ∈ compOf r S u :=
  mem_compOf.mpr (ReachIn.of_adj h hw hrw)

/-- No chain starts in `A` and ends in `B` when `A`, `B` are disjoint with no
edges between them and the chain stays inside `A ∪ B`. -/
theorem chain_not_cross {A B : Finset V} (hrs : ∀ a b, r a b → r b a)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ r a b) (hdisj : Disjoint A B) {l : List V}
    (hl : l.IsChain r) (hlS : ∀ x ∈ l, x ∈ A ∪ B) : ∀ {x y},
    l.head? = some x → l.getLast? = some y → x ∈ A → y ∈ B → False := by
  induction l with
  | nil => intro x y hx; simp at hx
  | cons a t ih =>
    intro x y hx hy hxA hyB
    simp only [List.head?_cons, Option.some_inj] at hx
    subst hx
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some_inj] at hy
      subst hy
      exact Finset.disjoint_left.mp hdisj hxA hyB
    | cons b s =>
      have hbS : b ∈ A ∪ B := hlS _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have hab : r a b := (List.isChain_cons.mp hl).1 _ (by simp)
      rcases Finset.mem_union.mp hbS with hbA | hbB
      · exact ih hl.tail (fun z hz ↦ hlS _ (List.mem_cons_of_mem _ hz)) rfl hy hbA hyB
      · exact hAB _ hxA _ hbB hab

/-- A connected set `C ⊆ S` cannot meet both sides of an edge-free split of `S`. -/
theorem comp_subset_or {S C A B : Finset V} (hrs : ∀ a b, r a b → r b a)
    (hCS : C ⊆ S) (hCconn : ∀ x ∈ C, ∀ y ∈ C, ReachIn r S x y)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ r a b) (hdisj : Disjoint A B)
    (hcov : S ⊆ A ∪ B) : C ⊆ A ∨ C ⊆ B := by
  by_contra h
  push_neg at h
  obtain ⟨x, hxC, hxA⟩ := Finset.not_subset.mp h.1
  obtain ⟨y, hyC, hyB⟩ := Finset.not_subset.mp h.2
  have hxB : x ∈ B := by
    rcases Finset.mem_union.mp (hcov (hCS hxC)) with h' | h'
    · exact absurd h' hxA
    · exact h'
  have hyA : y ∈ A := by
    rcases Finset.mem_union.mp (hcov (hCS hyC)) with h' | h'
    · exact h'
    · exact absurd h' hyB
  obtain ⟨l, hl, hlS, hh, ht⟩ := hCconn y hyC x hxC
  exact chain_not_cross hrs hAB hdisj hl (fun z hz ↦ hcov (hlS z hz)) hh ht hyA hxB

/-- A chain that stays inside `T` and starts inside `C` can never leave `C`
when `C` has no edges to `T \ C`. -/
theorem chain_stays_in {T C : Finset V}
    (hbnd : ∀ c ∈ C, ∀ z ∈ T \ C, ¬ r c z) {l : List V}
    (hl : l.IsChain r) (hlT : ∀ x ∈ l, x ∈ T) :
    ∀ u ∈ l.head?, u ∈ C → ∀ w ∈ l.getLast?, w ∈ C := by
  induction l with
  | nil => simp
  | cons a s ih =>
    intro u hu huC w hw
    simp only [List.head?_cons, Option.mem_some_iff] at hu
    subst hu
    cases s with
    | nil =>
      simp only [List.getLast?_singleton, Option.mem_some_iff] at hw
      rwa [← hw]
    | cons b s' =>
      have hbT : b ∈ T := hlT _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have hub : r a b := (List.isChain_cons.mp hl).1 b rfl
      have hbC : b ∈ C := by
        by_contra hbC
        exact hbnd _ huC _ (Finset.mem_sdiff.mpr ⟨hbT, hbC⟩) hub
      rw [List.getLast?_cons_cons] at hw
      exact ih hl.tail (fun z hz ↦ hlT _ (List.mem_cons_of_mem _ hz)) b rfl hbC _ hw

/-- If `u` reaches `w` inside `T` and `u` lies in a part `C` with no edges to
`T \ C`, then `w ∈ C`. -/
theorem not_reachIn_of_boundary {T C : Finset V} {u w : V}
    (hbnd : ∀ c ∈ C, ∀ z ∈ T \ C, ¬ r c z)
    (hu : u ∈ C) (hw : w ∈ T \ C) : ¬ ReachIn r T u w := by
  rintro ⟨l, hl, hlT, hh, ht⟩
  have hwC := chain_stays_in hbnd hl hlT u (by rw [hh]; rfl) hu w (by rw [ht]; rfl)
  exact (Finset.mem_sdiff.mp hw).2 hwC

/-- A set with a nonempty edge-free part `C` and another element is not
`r`-connected. -/
theorem not_connected_of_boundary {T C : Finset V}
    (hC : C ⊆ T) (hbnd : ∀ c ∈ C, ∀ z ∈ T \ C, ¬ r c z)
    (hCe : C.Nonempty) (hTe : (T \ C).Nonempty) :
    ∃ u ∈ T, ∃ w ∈ T, ¬ ReachIn r T u w := by
  obtain ⟨u, hu⟩ := hCe
  obtain ⟨w, hw⟩ := hTe
  exact ⟨u, hC hu, w, (Finset.mem_sdiff.mp hw).1,
    not_reachIn_of_boundary hbnd hu hw⟩

/-! ### Extremal partition (Pokrovskiy Lemma 3.4) -/

/-- Components inside `T` based at unreachable vertices are disjoint. -/
theorem disjoint_compOf {T : Finset V} {u v : V} (hrs : ∀ a b, r a b → r b a)
    (h : ¬ ReachIn r T u v) : Disjoint (compOf r T u) (compOf r T v) := by
  rw [Finset.disjoint_left]
  intro x hxu hxv
  rw [mem_compOf] at hxu hxv
  exact h (ReachIn.trans r hxu (ReachIn.symm r hrs hxv))

/-- A partition of `T` into a chain `P` and two sets `A`, `B` with no
`r`-edges between them, as in Pokrovskiy's Lemma 3.4. -/
def PokPAB (r : V → V → Prop) (T : Finset V) (v : V)
    (P : List V) (A B : Finset V) : Prop :=
  P.IsChain r ∧ P.Nodup ∧ (∀ x ∈ P, x ∈ T) ∧
    (P = [] ∨ P.head? = some v) ∧
    A ⊆ T ∧ B ⊆ T ∧
    Disjoint P.toFinset A ∧ Disjoint P.toFinset B ∧ Disjoint A B ∧
    (∀ x ∈ T, x ∈ P.toFinset ∨ x ∈ A ∨ x ∈ B) ∧
    (∀ a ∈ A, ∀ b ∈ B, ¬ r a b) ∧
    A.card ≤ B.card

/-- The lexicographic score used in the extremal choice of Lemma 3.4:
maximize `|A \ C|`, then `|A|`, then `|P|`, where `C` is the component of
`v` inside `T`. -/
noncomputable def pokScore (r : V → V → Prop) (T : Finset V) (v : V)
    (P : List V) (A : Finset V) : ℕ :=
  (A \ compOf r T v).card * (Fintype.card V + 1) ^ 2 +
    A.card * (Fintype.card V + 1) + P.length

/-- **Pokrovskiy Lemma 3.4.**  If `v` lies in a largest `r`-component of `T`,
then `T` can be partitioned into a chain `P` (empty or starting at `v`) and
two equal-sized sets `A`, `B` with no `r`-edges between them. -/
theorem pok_lemma34 (hrs : ∀ a b, r a b → r b a) (T : Finset V) (v : V)
    (hvT : v ∈ T)
    (hvmax : ∀ w ∈ T, (compOf r T w).card ≤ (compOf r T v).card) :
    ∃ P A B, PokPAB r T v P A B ∧ A.card = B.card := by
  classical
  have hV : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  set M := Fintype.card V + 1 with hMdef
  have hM : 2 ≤ M := by omega
  have hMle : M - 1 + 1 = M := by omega
  -- Every valid partition has score below `M ^ 3`.
  have hbnd : ∀ P A B, PokPAB r T v P A B → pokScore r T v P A < M ^ 3 := by
    intro P A B h
    have ha : (A \ compOf r T v).card ≤ M - 1 := by
      have h1 : (A \ compOf r T v).card ≤ A.card :=
        Finset.card_le_card Finset.sdiff_subset
      have h2 : A.card ≤ Fintype.card V := Finset.card_le_univ A
      omega
    have hb : A.card ≤ M - 1 := by
      have := Finset.card_le_univ A; omega
    have hc : P.length ≤ M - 1 := by
      have := h.2.1.length_le_card; omega
    have e1 : (A \ compOf r T v).card * M ^ 2 ≤ (M - 1) * M ^ 2 :=
      Nat.mul_le_mul_right _ ha
    have e2 : A.card * M ≤ (M - 1) * M := Nat.mul_le_mul_right _ hb
    have key : (M - 1) * M ^ 2 + (M - 1) * M + (M - 1) < M ^ 3 := by
      have h1 : (M - 1) * M + (M - 1) < M * M := by
        have hlt : (M - 1) * M + (M - 1) < (M - 1) * M + M :=
          Nat.add_lt_add_left (by omega) _
        have heq : (M - 1) * M + M = M * M := by
          calc (M - 1) * M + M = (M - 1) * M + 1 * M := by rw [one_mul]
            _ = ((M - 1) + 1) * M := (Nat.add_mul ..).symm
            _ = M * M := by rw [hMle]
        omega
      have h2 : (M - 1) * M ^ 2 + ((M - 1) * M + (M - 1)) <
          (M - 1) * M ^ 2 + M * M := Nat.add_lt_add_left h1 _
      have heq : (M - 1) * M ^ 2 + M * M = M ^ 3 := by
        calc (M - 1) * M ^ 2 + M * M = (M - 1) * M ^ 2 + 1 * M ^ 2 := by
              rw [one_mul, pow_two]
          _ = ((M - 1) + 1) * M ^ 2 := (Nat.add_mul ..).symm
          _ = M * M ^ 2 := by rw [hMle]
          _ = M ^ 3 := by ring
      omega
    unfold pokScore
    rw [← hMdef]
    omega
  -- The trivial partition witnesses feasibility.
  have hw0 : PokPAB r T v [] ∅ T := by
    refine ⟨by simp, by simp, by simp, Or.inl rfl, Finset.empty_subset _,
      Finset.Subset.refl _, by simp, by simp, Finset.disjoint_empty_left _,
      fun x hx ↦ Or.inr (Or.inr hx), fun a ha ↦ by simp at ha, Nat.zero_le _⟩
  have hscore0 : pokScore r T v [] (∅ : Finset V) = 0 := by
    unfold pokScore; simp
  have hspec := Nat.findGreatest_spec
    (P := fun m ↦ ∃ P A B, PokPAB r T v P A B ∧ pokScore r T v P A = m)
    (n := M ^ 3) (Nat.zero_le _)
    (m := 0) ⟨[], ∅, T, hw0, hscore0⟩
  obtain ⟨P, A, B, hPAB, hscore⟩ := hspec
  obtain ⟨hPc, hPnd, hPT, hPhd, hAT, hBT, hdPA, hdPB, hdAB, hcov, hAB, hAle⟩ :=
    hPAB
  refine ⟨P, A, B,
    ⟨hPc, hPnd, hPT, hPhd, hAT, hBT, hdPA, hdPB, hdAB, hcov, hAB, hAle⟩, ?_⟩
  -- A helper for the final contradiction: any strictly-better valid partition
  -- is impossible.
  have hmax : ∀ P' A' B', PokPAB r T v P' A' B' →
      pokScore r T v P' A' ≤ pokScore r T v P A := by
    intro P' A' B' h'
    have hle := Nat.le_findGreatest
      (P := fun m ↦ ∃ P A B, PokPAB r T v P A B ∧ pokScore r T v P A = m)
      (le_of_lt (hbnd _ _ _ h'))
      ⟨P', A', B', h', rfl⟩
    rw [hscore]; exact hle
  by_contra hne
  have hlt : A.card < B.card := Nat.lt_of_le_of_ne hAle hne
  set C := compOf r T v with hCdef
  have hCT : C ⊆ T := compOf_subset
  have hCle : C.card ≤ M - 1 := by
    have := Finset.card_le_univ C; omega
  have hCconn : ∀ x ∈ C, ∀ y ∈ C, ReachIn r T x y := by
    intro x hx y hy
    rw [hCdef, mem_compOf] at hx hy
    exact ReachIn.trans r (ReachIn.symm r hrs hx) hy
  by_cases hPe : P = []
  · -- Case `P = []`: the component `C` of `v` sits on one side.
    subst hPe
    have hT : T ⊆ A ∪ B := fun x hx ↦ by
      rcases hcov x hx with h | h | h
      · simp at h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ h
    have hBe : B.Nonempty := by
      rw [← Finset.card_pos]; omega
    have hC : C ⊆ A ∨ C ⊆ B :=
      comp_subset_or hrs hCT hCconn hAB hdAB hT
    rcases hC with hCA | hCB
    · -- `C ⊆ A`: move `C` to `B` and a component `D ⊆ B` to `A`.
      obtain ⟨d, hdB⟩ := hBe
      have hdT : d ∈ T := hBT hdB
      have hdD : d ∈ compOf r T d := mem_compOf_self hdT
      have hDconn : ∀ x ∈ compOf r T d, ∀ y ∈ compOf r T d,
          ReachIn r T x y := by
        intro x hx y hy
        rw [mem_compOf] at hx hy
        exact ReachIn.trans r (ReachIn.symm r hrs hx) hy
      have hDB : compOf r T d ⊆ B := by
        rcases comp_subset_or hrs compOf_subset hDconn hAB hdAB hT
          with h | h
        · exact absurd (h hdD) (Finset.disjoint_left.mp hdAB.symm hdB)
        · exact h
      have hdC : d ∉ C := fun h ↦ Finset.disjoint_left.mp hdAB (hCA h) hdB
      set D := compOf r T d with hDdef
      have hDC : Disjoint D C :=
        disjoint_compOf hrs (fun h ↦
          hdC (mem_compOf.mpr (ReachIn.symm r hrs h)))
      have hDle : D.card ≤ C.card := hvmax d hdT
      have hDne : D.Nonempty := ⟨d, hdD⟩
      have hvalid' : PokPAB r T v [] (A \ C ∪ D) (B \ D ∪ C) := by
        refine ⟨by simp, by simp, by simp, Or.inl rfl, ?_, ?_, by simp,
          by simp, ?_, ?_, ?_, ?_⟩
        · exact Finset.union_subset (Finset.sdiff_subset.trans hAT)
            compOf_subset
        · exact Finset.union_subset (Finset.sdiff_subset.trans hBT) hCT
        · rw [Finset.disjoint_left]
          intro x hxA' hxB'
          rcases Finset.mem_union.mp hxA' with hxAC | hxD
          · rcases Finset.mem_union.mp hxB' with hxBD | hxC
            · exact Finset.disjoint_left.mp hdAB
                (Finset.mem_sdiff.mp hxAC).1 (Finset.mem_sdiff.mp hxBD).1
            · exact (Finset.mem_sdiff.mp hxAC).2 hxC
          · rcases Finset.mem_union.mp hxB' with hxBD | hxC
            · exact (Finset.mem_sdiff.mp hxBD).2 hxD
            · exact Finset.disjoint_left.mp hDC hxD hxC
        · intro x hx
          rcases hcov x hx with h | hxA | hxB
          · simp at h
          · by_cases hxC : x ∈ C
            · exact Or.inr (Or.inr (Finset.mem_union_right _ hxC))
            · exact Or.inr (Or.inl (Finset.mem_union_left _
                (Finset.mem_sdiff.mpr ⟨hxA, hxC⟩)))
          · by_cases hxD : x ∈ D
            · exact Or.inr (Or.inl (Finset.mem_union_right _ hxD))
            · exact Or.inr (Or.inr (Finset.mem_union_left _
                (Finset.mem_sdiff.mpr ⟨hxB, hxD⟩)))
        · intro a ha b hb hab
          rcases Finset.mem_union.mp ha with haAC | haD
          · rcases Finset.mem_union.mp hb with hbBD | hbC
            · exact hAB _ (Finset.mem_sdiff.mp haAC).1 _
                (Finset.mem_sdiff.mp hbBD).1 hab
            · have haT : a ∈ T := hAT (Finset.mem_sdiff.mp haAC).1
              have haC : a ∈ C := mem_compOf_of_adj
                (mem_compOf.mp hbC) haT (hrs _ _ hab)
              exact (Finset.mem_sdiff.mp haAC).2 haC
          · rcases Finset.mem_union.mp hb with hbBD | hbC
            · have hbT : b ∈ T := hBT (Finset.mem_sdiff.mp hbBD).1
              have hbD : b ∈ D :=
                mem_compOf_of_adj (mem_compOf.mp haD) hbT hab
              exact (Finset.mem_sdiff.mp hbBD).2 hbD
            · have haT : a ∈ T := compOf_subset haD
              have haC : a ∈ C :=
                mem_compOf_of_adj (mem_compOf.mp hbC) haT (hrs _ _ hab)
              exact Finset.disjoint_left.mp hDC haD haC
        · have h1 : (A \ C ∪ D).card = (A \ C).card + D.card := by
            rw [Finset.card_union_of_disjoint]
            rw [Finset.disjoint_left]
            intro x hxAC hxD
            exact Finset.disjoint_left.mp hdAB (Finset.mem_sdiff.mp hxAC).1
              (hDB hxD)
          have h2 : (B \ D ∪ C).card = (B \ D).card + C.card := by
            rw [Finset.card_union_of_disjoint]
            rw [Finset.disjoint_left]
            intro x hxBD hxC
            exact Finset.disjoint_left.mp hdAB (hCA hxC)
              (Finset.mem_sdiff.mp hxBD).1
          have h3 : (A \ C).card = A.card - C.card :=
            Finset.card_sdiff_of_subset hCA
          have h4 : (B \ D).card = B.card - D.card :=
            Finset.card_sdiff_of_subset hDB
          omega
      -- The new partition has a strictly larger score: contradiction.
      have hgt : pokScore r T v [] A < pokScore r T v [] (A \ C ∪ D) := by
        have h1 : (A \ C ∪ D).card = (A \ C).card + D.card := by
          rw [Finset.card_union_of_disjoint]
          rw [Finset.disjoint_left]
          intro x hxAC hxD
          exact Finset.disjoint_left.mp hdAB (Finset.mem_sdiff.mp hxAC).1
            (hDB hxD)
        have h2 : ((A \ C ∪ D) \ C).card = (A \ C).card + D.card := by
          have hsub : (A \ C ∪ D) \ C = A \ C ∪ D := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_union]
            constructor
            · intro h; exact h.1
            · intro h
              rcases h with hxAC | hxD
              · exact ⟨Or.inl hxAC, hxAC.2⟩
              · exact ⟨Or.inr hxD, fun hxC ↦
                  Finset.disjoint_left.mp hDC hxD hxC⟩
          rw [hsub]; exact h1
        have h3 : (A \ C).card = A.card - C.card :=
          Finset.card_sdiff_of_subset hCA
        have h4 : C.card ≤ A.card := Finset.card_le_card hCA
        have h5 : 1 ≤ D.card := Finset.card_pos.mpr hDne
        have h6 : C.card * M ≤ M ^ 2 := by
          calc C.card * M ≤ (M - 1) * M := Nat.mul_le_mul_right _ hCle
            _ ≤ M * M := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
            _ = M ^ 2 := by rw [pow_two]
        unfold pokScore
        rw [← hCdef, ← hMdef]
        have e1 : ((A \ C ∪ D) \ C).card * M ^ 2 =
            (A \ C).card * M ^ 2 + D.card * M ^ 2 := by rw [h2, Nat.add_mul]
        have e2 : (A \ C ∪ D).card * M =
            (A \ C).card * M + D.card * M := by rw [h1, Nat.add_mul]
        have e5 : A.card * M = (A \ C).card * M + C.card * M := by
          have hA : A.card = (A \ C).card + C.card := by omega
          rw [hA, Nat.add_mul]
        have h7 : M ^ 2 ≤ D.card * M ^ 2 := Nat.le_mul_of_pos_left _ h5
        have h8 : M ≤ D.card * M := Nat.le_mul_of_pos_left _ h5
        omega
      exact absurd (hmax _ _ _ hvalid') (by omega)
    · -- `C ⊆ B`: `v ∈ B`; move `v` onto the path.
      have hvC : v ∈ C := mem_compOf_self hvT
      have hvB : v ∈ B := hCB hvC
      have hvalid' : PokPAB r T v [v] A (B \ {v}) := by
        refine ⟨by simp, by simp, ?_, Or.inr rfl, hAT, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_⟩
        · intro x hx
          rw [List.mem_singleton] at hx
          subst hx
          exact hvT
        · exact Finset.sdiff_subset.trans hBT
        · rw [List.toFinset_cons, List.toFinset_nil]
          rw [Finset.disjoint_left]
          intro x hx
          simp at hx
          subst hx
          exact Finset.disjoint_left.mp hdAB.symm hvB
        · rw [List.toFinset_cons, List.toFinset_nil]
          rw [Finset.disjoint_left]
          intro x hx hxB
          simp at hx
          subst hx
          exact (Finset.mem_sdiff.mp hxB).2 (Finset.mem_singleton_self _)
        · rw [Finset.disjoint_left]
          intro x hxA hxB
          exact Finset.disjoint_left.mp hdAB hxA (Finset.mem_sdiff.mp hxB).1
        · intro x hx
          rcases hcov x hx with h | hxA | hxB
          · simp at h
          · exact Or.inr (Or.inl hxA)
          · by_cases hxv : x = v
            · subst hxv
              exact Or.inl (by simp)
            · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨hxB,
                fun hx' ↦ hxv (Finset.mem_singleton.mp hx')⟩))
        · intro a ha b hb
          exact hAB _ ha _ (Finset.mem_sdiff.mp hb).1
        · have h1 : (B \ {v}).card = B.card - 1 := by
            have := Finset.card_sdiff_of_subset
              (Finset.singleton_subset_iff.mpr hvB)
            rwa [Finset.card_singleton] at this
          omega
      have hgt : pokScore r T v [] A < pokScore r T v [v] A := by
        unfold pokScore
        simp only [List.length_nil, List.length_cons]
        omega
      exact absurd (hmax _ _ _ hvalid') (by omega)
  · -- Case `P ≠ []`: let `u` be the last vertex of `P`.
    obtain ⟨u, hu⟩ : ∃ u, P.getLast? = some u :=
      ⟨P.getLast hPe, List.getLast?_eq_getLast_of_ne_nil hPe⟩
    have huP : u ∈ P := by
      have hmem : u ∈ P.getLast? := by rw [hu]; rfl
      exact List.mem_of_mem_getLast? hmem
    have huT : u ∈ T := hPT _ huP
    have hPhv : P.head? = some v := by
      rcases hPhd with h | h
      · exact absurd h hPe
      · exact h
    by_cases hw : ∃ w ∈ B, r u w
    · -- Extend `P` by a vertex of `B`.
      obtain ⟨w, hwB, hruw⟩ := hw
      have hwT : w ∈ T := hBT hwB
      have hwP : w ∉ P := fun h ↦
        Finset.disjoint_left.mp hdPB (List.mem_toFinset.mpr h) hwB
      have hvalid' : PokPAB r T v (P ++ [w]) A (B \ {w}) := by
        refine ⟨?_, ?_, ?_, ?_, hAT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.isChain_append]
          refine ⟨hPc, by simp, fun x hx y hy ↦ ?_⟩
          rw [List.head?_cons, Option.mem_some_iff] at hy
          subst hy
          rw [hu, Option.mem_some_iff] at hx
          subst hx
          exact hruw
        · rw [List.nodup_append']
          refine ⟨hPnd, by simp, ?_⟩
          rw [List.disjoint_left]
          intro x hx hw'
          rw [List.mem_singleton] at hw'
          subst hw'
          exact hwP hx
        · intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · exact hPT _ hx
          · rw [List.mem_singleton] at hx; subst hx; exact hwT
        · exact Or.inr (by rw [List.head?_append_of_ne_nil _ hPe]; exact hPhv)
        · exact Finset.sdiff_subset.trans hBT
        · rw [List.toFinset_append]
          rw [Finset.disjoint_left]
          intro x hx hxA
          rcases Finset.mem_union.mp hx with hxP | hxw
          · exact Finset.disjoint_left.mp hdPA hxP hxA
          · simp at hxw
            subst hxw
            exact Finset.disjoint_left.mp hdAB hxA hwB
        · rw [List.toFinset_append]
          rw [Finset.disjoint_left]
          intro x hx hxB
          rcases Finset.mem_union.mp hx with hxP | hxw
          · exact Finset.disjoint_left.mp hdPB hxP (Finset.mem_sdiff.mp hxB).1
          · simp at hxw
            subst hxw
            exact (Finset.mem_sdiff.mp hxB).2 (Finset.mem_singleton_self _)
        · rw [Finset.disjoint_left]
          intro x hxA hxB
          exact Finset.disjoint_left.mp hdAB hxA (Finset.mem_sdiff.mp hxB).1
        · intro x hx
          rcases hcov x hx with hxP | hxA | hxB
          · exact Or.inl (by
              rw [List.toFinset_append]
              exact Finset.mem_union_left _ hxP)
          · exact Or.inr (Or.inl hxA)
          · by_cases hxw : x = w
            · subst hxw
              exact Or.inl (by simp)
            · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨hxB,
                fun hx' ↦ hxw (Finset.mem_singleton.mp hx')⟩))
        · intro a ha b hb
          exact hAB _ ha _ (Finset.mem_sdiff.mp hb).1
        · have h1 : (B \ {w}).card = B.card - 1 := by
            have := Finset.card_sdiff_of_subset
              (Finset.singleton_subset_iff.mpr hwB)
            rwa [Finset.card_singleton] at this
          omega
      have hgt : pokScore r T v P A < pokScore r T v (P ++ [w]) A := by
        unfold pokScore
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      exact absurd (hmax _ _ _ hvalid') (by omega)
    · -- Move the last vertex of `P` into `A`.
      push_neg at hw
      have hmem : u ∈ P.getLast? := by rw [hu]; rfl
      have hsplit : P = P.dropLast ++ [u] :=
        (List.dropLast_append_getLast? _ hmem).symm
      have hvalid' : PokPAB r T v P.dropLast (A ∪ {u}) B := by
        refine ⟨?_, ?_, ?_, ?_, ?_, hBT, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact (List.isChain_append.mp (hsplit ▸ hPc)).1
        · exact (List.nodup_append'.mp (hsplit ▸ hPnd)).1
        · intro x hx
          exact hPT _ (List.mem_of_mem_dropLast hx)
        · obtain ⟨a0, t0, hPt⟩ := List.exists_cons_of_ne_nil hPe
          subst hPt
          cases t0 with
          | nil => exact Or.inl (by simp)
          | cons b0 s0 =>
            right
            simp only [List.head?_cons, Option.some_inj] at hPhv
            subst hPhv
            rw [List.dropLast_cons_cons, List.head?_cons]
        · exact Finset.union_subset hAT (Finset.singleton_subset_iff.mpr huT)
        · rw [Finset.disjoint_left]
          intro x hxP' hxA'
          have hxP : x ∈ P.toFinset := by
            have hxd : x ∈ P.dropLast := by simpa using hxP'
            simpa using List.mem_of_mem_dropLast hxd
          rcases Finset.mem_union.mp hxA' with hxA | hxu
          · exact Finset.disjoint_left.mp hdPA hxP hxA
          · rw [Finset.mem_singleton] at hxu
            subst hxu
            -- `x ∈ P.dropLast` contradicts `P.Nodup`
            have hnd := List.nodup_append'.mp (hsplit ▸ hPnd)
            exact hnd.2.2 (by simpa using hxP') (by simp)
        · rw [Finset.disjoint_left]
          intro x hxP' hxB
          have hxP : x ∈ P.toFinset := by
            have hxd : x ∈ P.dropLast := by simpa using hxP'
            simpa using List.mem_of_mem_dropLast hxd
          exact Finset.disjoint_left.mp hdPB hxP hxB
        · rw [Finset.disjoint_left]
          intro x hxA' hxB
          rcases Finset.mem_union.mp hxA' with hxA | hxu
          · exact Finset.disjoint_left.mp hdAB hxA hxB
          · rw [Finset.mem_singleton] at hxu
            subst hxu
            exact Finset.disjoint_left.mp hdPB
              (by simpa using huP) hxB
        · intro x hx
          rcases hcov x hx with hxP | hxA | hxB
          · have hxPl : x ∈ P := by simpa using hxP
            by_cases hxu : x = u
            · subst hxu
              exact Or.inr (Or.inl (Finset.mem_union_right _
                (Finset.mem_singleton.mpr rfl)))
            · left
              have hxd : x ∈ P.dropLast ++ [u] := hsplit ▸ hxPl
              rw [List.mem_append] at hxd
              rcases hxd with h | h
              · simpa using h
              · exact absurd (List.mem_singleton.mp h) hxu
          · exact Or.inr (Or.inl (Finset.mem_union_left _ hxA))
          · exact Or.inr (Or.inr hxB)
        · intro a ha b hb hab
          rcases Finset.mem_union.mp ha with haA | hau
          · exact hAB _ haA _ hb hab
          · rw [Finset.mem_singleton] at hau
            subst hau
            exact hw _ hb hab
        · have h1 : (A ∪ {u}).card = A.card + 1 := by
            rw [Finset.card_union_of_disjoint, Finset.card_singleton]
            rw [Finset.disjoint_left]
            intro x hxA hxu
            rw [Finset.mem_singleton] at hxu
            subst hxu
            exact Finset.disjoint_left.mp hdPA
              (by simpa using huP) hxA
          omega
      have hgt : pokScore r T v P A < pokScore r T v P.dropLast (A ∪ {u}) := by
        have hsub : A \ C ⊆ (A ∪ {u}) \ C :=
          Finset.sdiff_subset_sdiff Finset.subset_union_left (Subset.refl _)
        have hcard : (A ∪ {u}).card = A.card + 1 := by
          rw [Finset.card_union_of_disjoint, Finset.card_singleton]
          rw [Finset.disjoint_left]
          intro x hxA hxu
          rw [Finset.mem_singleton] at hxu
          subst hxu
          exact Finset.disjoint_left.mp hdPA
            (by simpa using huP) hxA
        have hlen : P.dropLast.length = P.length - 1 := List.length_dropLast
        have hlenpos : 1 ≤ P.length := List.length_pos_of_ne_nil hPe
        have hcle : (A \ C).card * M ^ 2 ≤ ((A ∪ {u}) \ C).card * M ^ 2 :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        have e : (A.card + 1) * M = A.card * M + M := by
          rw [Nat.add_mul, one_mul]
        unfold pokScore
        rw [← hCdef, ← hMdef, hcard, hlen]
        omega
      exact absurd (hmax _ _ _ hvalid') (by omega)

/-! ### Alternating (interleaved) chains -/

/-- Interleave two lists starting with `xs`:
`interleave [a₁,a₂,…] [b₁,b₂,…] = [a₁,b₁,a₂,b₂,…]`.  When the longer list has
at most one extra element, the result alternates. -/
def interleave : List V → List V → List V
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => x :: y :: interleave xs ys

theorem interleave_length (xs ys : List V) :
    (interleave xs ys).length = xs.length + ys.length := by
  induction xs generalizing ys with
  | nil => simp [interleave]
  | cons x xs ih =>
    cases ys with
    | nil => simp [interleave]
    | cons y ys => simp only [interleave, List.length_cons, ih]; omega

theorem mem_interleave {x : V} {xs ys : List V} :
    x ∈ interleave xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  induction xs generalizing ys with
  | nil => simp [interleave]
  | cons a xs ih =>
    cases ys with
    | nil => simp [interleave]
    | cons b ys => simp only [interleave, List.mem_cons, ih]; tauto

theorem interleave_nodup {xs ys : List V} (hxs : xs.Nodup) (hys : ys.Nodup)
    (hd : ∀ a ∈ xs, a ∉ ys) : (interleave xs ys).Nodup := by
  induction xs generalizing ys with
  | nil => simpa [interleave]
  | cons x xs ih =>
    cases ys with
    | nil => simpa only [interleave] using hxs
    | cons y ys =>
      rw [interleave, List.nodup_cons, List.nodup_cons]
      obtain ⟨hx1, hx2⟩ := List.nodup_cons.mp hxs
      obtain ⟨hy1, hy2⟩ := List.nodup_cons.mp hys
      refine ⟨fun hxy ↦ ?_, fun hmem ↦ ?_, ?_⟩
      · rw [List.mem_cons] at hxy
        rcases hxy with rfl | hmem
        · exact hd _ List.mem_cons_self List.mem_cons_self
        · rw [mem_interleave] at hmem
          rcases hmem with h | h
          · exact hx1 h
          · exact hd _ List.mem_cons_self (List.mem_cons_of_mem _ h)
      · rw [mem_interleave] at hmem
        rcases hmem with h | h
        · exact hd _ (List.mem_cons_of_mem _ h) List.mem_cons_self
        · exact hy1 h
      · exact ih hx2 hy2 fun a ha hb ↦
          hd _ (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb)

/-- If every `xs`–`ys` pair is `r`-related (in both directions) and
`ys.length ≤ xs.length ≤ ys.length + 1`, the interleaved list is an
`r`-chain. -/
theorem interleave_isChain {xs ys : List V}
    (h : ∀ a ∈ xs, ∀ b ∈ ys, r a b) (hs : ∀ a ∈ xs, ∀ b ∈ ys, r b a)
    (hle : xs.length ≤ ys.length + 1) (hge : ys.length ≤ xs.length) :
    (interleave xs ys).IsChain r := by
  induction xs generalizing ys with
  | nil =>
    have hys : ys = [] := by
      cases ys with
      | nil => rfl
      | cons y ys => simp at hge
    simp [hys, interleave]
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons x' xs' => simp at hle
      simp [hxs, interleave]
    | cons y ys =>
      rw [interleave, List.isChain_cons]
      refine ⟨?_, ?_⟩
      · intro z hz
        simp only [List.head?_cons, Option.mem_some_iff] at hz
        subst hz
        exact h _ List.mem_cons_self _ List.mem_cons_self
      · rw [List.isChain_cons]
        refine ⟨?_, ?_⟩
        · intro z hz
          cases xs with
          | nil =>
            have hys' : ys = [] := by
              cases ys with
              | nil => rfl
              | cons => simp at hge
            subst hys'
            simp [interleave] at hz
          | cons x' xs' =>
            cases ys with
            | nil =>
              simp only [interleave, List.head?_cons, Option.mem_some_iff] at hz
              subst hz
              exact hs _ (List.mem_cons_of_mem _ List.mem_cons_self)
                _ List.mem_cons_self
            | cons y' ys' =>
              simp only [interleave, List.head?_cons, Option.mem_some_iff] at hz
              subst hz
              exact hs _ (List.mem_cons_of_mem _ List.mem_cons_self)
                _ List.mem_cons_self
        · cases xs with
          | nil =>
            have hys' : ys = [] := by
              cases ys with
              | nil => rfl
              | cons => simp at hge
            simp [hys', interleave]
          | cons x' xs' =>
            apply ih
            · intro a ha b hb
              exact h _ (List.mem_cons_of_mem _ ha) _ (List.mem_cons_of_mem _ hb)
            · intro a ha b hb
              exact hs _ (List.mem_cons_of_mem _ ha) _ (List.mem_cons_of_mem _ hb)
            · simp only [List.length_cons] at hle ⊢; omega
            · simp only [List.length_cons] at hge ⊢; omega

/-- The head of `interleave xs ys` is the head of `xs` (when `xs ≠ []`). -/
theorem interleave_head? {xs ys : List V} (hxs : xs ≠ []) :
    (interleave xs ys).head? = xs.head? := by
  cases xs with
  | nil => exact absurd rfl hxs
  | cons x xs =>
    cases ys with
    | nil => rfl
    | cons y ys => rfl

/-- `getLast?` of a cons whose tail is nonempty is the tail's `getLast?`. -/
theorem getLast?_cons_ne_nil {a : V} {l : List V} (hl : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b l => rfl

/-- An interleaved list is nonempty when `xs` is nonempty. -/
theorem interleave_ne_nil {xs ys : List V} (hxs : xs ≠ []) :
    interleave xs ys ≠ [] := by
  cases xs with
  | nil => exact absurd rfl hxs
  | cons x xs =>
    cases ys with
    | nil => simp [interleave]
    | cons y ys => simp [interleave]

/-- For equal-length inputs, the interleaved list ends with `ys`' last. -/
theorem interleave_getLast?_eq {xs ys : List V} (h : xs.length = ys.length) :
    (interleave xs ys).getLast? = ys.getLast? := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      rw [interleave]
      cases xs with
      | nil =>
        have hys : ys = [] := by
          cases ys with
          | nil => rfl
          | cons => simp at h
        subst hys
        rfl
      | cons x' xs' =>
        have hys : ys ≠ [] := by
          intro hcon
          simp only [hcon, List.length_cons, List.length_nil] at h
          omega
        rw [getLast?_cons_ne_nil (List.cons_ne_nil _ _),
            getLast?_cons_ne_nil (interleave_ne_nil (List.cons_ne_nil _ _)),
            getLast?_cons_ne_nil hys]
        exact ih (by simp only [List.length_cons] at h ⊢; omega)

/-- If every `xs`–`ys` pair is `c`-adjacent (in the `Color.adjXY` sense) and
the lengths differ by at most one, `interleave xs ys` is a `c`-colored
alternating chain. -/
theorem interleave_adjXY_isChain {xs ys : List V} {c : Color}
    (h : ∀ a ∈ xs, ∀ b ∈ ys, Color.adjXY G X Y c a b)
    (hle : xs.length ≤ ys.length + 1) (hge : ys.length ≤ xs.length) :
    (interleave xs ys).IsChain (Color.adjXY G X Y c) :=
  interleave_isChain (fun a ha b hb ↦ h _ ha _ hb)
    (fun a ha b hb ↦ Color.adjXY.symm (h _ ha _ hb)) hle hge

/-- If every `xs`–`ys` pair is blue and `xs ⊆ X`, `ys ⊆ Y`, the interleaved
list is a blue alternating chain. -/
theorem interleave_blue_isChain {xs ys : List V}
    (hxs : ∀ x ∈ xs, x ∈ X) (hys : ∀ y ∈ ys, y ∈ Y)
    (hblue : ∀ a ∈ xs, ∀ b ∈ ys, ¬ G.Adj a b)
    (hle : xs.length ≤ ys.length + 1) (hge : ys.length ≤ xs.length) :
    (interleave xs ys).IsChain (Color.adjXY G X Y .blue) :=
  interleave_adjXY_isChain
    (fun a ha b hb ↦ ⟨Or.inl ⟨hxs _ ha, hys _ hb⟩, hblue _ ha _ hb⟩) hle hge

/-- For `xs` one longer than `ys`, the interleaved list ends with `xs`' last. -/
theorem interleave_getLast?_succ {xs ys : List V} (h : xs.length = ys.length + 1) :
    (interleave xs ys).getLast? = xs.getLast? := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons => simp at h
      subst hxs
      rfl
    | cons y ys =>
      rw [interleave]
      cases xs with
      | nil =>
        simp only [List.length_cons, List.length_nil] at h
        omega
      | cons x' xs' =>
        rw [getLast?_cons_ne_nil (List.cons_ne_nil _ _),
            getLast?_cons_ne_nil (interleave_ne_nil (List.cons_ne_nil _ _)),
            List.getLast?_cons_cons]
        exact ih (by simp only [List.length_cons] at h ⊢; omega)

/-- Package a nonempty nodup `Color.adjXY`-chain as a `VertPath`. -/
theorem vertPath_of_chain {c : Color} {l : List V} (hne : l ≠ []) (hnd : l.Nodup)
    (hch : l.IsChain (Color.adjXY G X Y c)) :
    ∃ p : VertPath V, p.toList.IsChain (Color.adjXY G X Y c) ∧
      p.toList.length = l.length :=
  ⟨⟨l, hne, hnd⟩, hch, rfl⟩

/-- The red counterpart of `blue_long_path`: in a red-complete bipartite
pair `A ⊆ X`, `B ⊆ Y` of nonempty finsets there is a red alternating path
on `min (|A|+|B|) (2·min(|A|,|B|)+1)` vertices. -/
theorem red_long_path {A B : Finset V} (hXY : Disjoint X Y)
    (hAX : A ⊆ X) (hBY : B ⊆ Y)
    (hb : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ p : VertPath V, p.toList.IsChain (Color.adjXY G X Y .red) ∧
      p.toList.length = min (A.card + B.card) (2 * min A.card B.card + 1) := by
  rcases Nat.lt_or_ge B.card A.card with hlt | hge
  · have hBA : B.card ≤ A.card := hlt.le
    have hmem : ∀ a ∈ A.toList.take (B.card + 1), a ∈ A :=
      fun a ha ↦ Finset.mem_toList.mp ((List.take_sublist _ _).mem ha)
    obtain ⟨p, hch, hlen⟩ := vertPath_of_chain
      (interleave_ne_nil (by
        intro hcon
        have hxlen : (A.toList.take (B.card + 1)).length = min (B.card + 1) A.card := by
          rw [List.length_take, Finset.length_toList]
        rw [hcon, List.length_nil] at hxlen
        have hpos : 0 < min (B.card + 1) A.card :=
          lt_min (Nat.succ_pos _) (Finset.Nonempty.card_pos hA)
        omega))
      (interleave_nodup
        ((List.take_sublist _ _).nodup (Finset.nodup_toList A))
        (Finset.nodup_toList B)
        (fun a ha hbB ↦
          (Disjoint.notMem_left hXY (hAX (hmem _ ha)))
            (hBY (Finset.mem_toList.mp hbB))))
      (interleave_adjXY_isChain (c := .red)
        (fun a ha b hbB ↦
          ⟨Or.inl ⟨hAX (hmem _ ha), hBY (Finset.mem_toList.mp hbB)⟩,
           hb _ (hmem _ ha) _ (Finset.mem_toList.mp hbB)⟩)
        (by simp only [List.length_take, Finset.length_toList]; omega)
        (by simp only [List.length_take, Finset.length_toList]; omega))
    refine ⟨p, hch, ?_⟩
    rw [hlen]
    simp only [interleave_length, List.length_take, Finset.length_toList,
      min_eq_right hBA]
    omega
  · have hmem : ∀ b ∈ B.toList.take (A.card + 1), b ∈ B :=
      fun b hb' ↦ Finset.mem_toList.mp ((List.take_sublist _ _).mem hb')
    obtain ⟨p, hch, hlen⟩ := vertPath_of_chain
      (interleave_ne_nil (by
        intro hcon
        have hxlen : (B.toList.take (A.card + 1)).length = min (A.card + 1) B.card := by
          rw [List.length_take, Finset.length_toList]
        rw [hcon, List.length_nil] at hxlen
        have hpos : 0 < min (A.card + 1) B.card :=
          lt_min (Nat.succ_pos _) (Finset.Nonempty.card_pos hB)
        omega))
      (interleave_nodup
        ((List.take_sublist _ _).nodup (Finset.nodup_toList B))
        (Finset.nodup_toList A)
        (fun a ha hbA ↦
          (Disjoint.notMem_right hXY (hBY (hmem _ ha)))
            (hAX (Finset.mem_toList.mp hbA))))
      (interleave_adjXY_isChain (c := .red)
        (fun a ha b hbA ↦
          ⟨Or.inr ⟨hBY (hmem _ ha), hAX (Finset.mem_toList.mp hbA)⟩,
           (hb _ (Finset.mem_toList.mp hbA) _ (hmem _ ha)).symm⟩)
        (by simp only [List.length_take, Finset.length_toList]; omega)
        (by simp only [List.length_take, Finset.length_toList]; omega))
    refine ⟨p, hch, ?_⟩
    rw [hlen]
    simp only [interleave_length, List.length_take, Finset.length_toList,
      min_eq_left hge]
    omega

/-- In a blue-complete bipartite pair `A ⊆ X`, `B ⊆ Y` of nonempty finsets,
there is a blue alternating path on `min (|A|+|B|) (2·min(|A|,|B|)+1)`
vertices (the maximum possible in `K_{|A|,|B|}`). -/
theorem blue_long_path {A B : Finset V} (hXY : Disjoint X Y)
    (hAX : A ⊆ X) (hBY : B ⊆ Y)
    (hb : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ p : VertPath V, p.toList.IsChain (Color.adjXY G X Y .blue) ∧
      p.toList.length = min (A.card + B.card) (2 * min A.card B.card + 1) := by
  rcases Nat.lt_or_ge B.card A.card with hlt | hge
  · -- `B.card < A.card`, so `B.card ≤ A.card`: path starts in `X`.
    have hBA : B.card ≤ A.card := hlt.le
    have hmem : ∀ a ∈ A.toList.take (B.card + 1), a ∈ A :=
      fun a ha ↦ Finset.mem_toList.mp ((List.take_sublist _ _).mem ha)
    obtain ⟨p, hch, hlen⟩ := vertPath_of_chain
      (interleave_ne_nil (by
        intro hcon
        have hxlen : (A.toList.take (B.card + 1)).length = min (B.card + 1) A.card := by
          rw [List.length_take, Finset.length_toList]
        rw [hcon, List.length_nil] at hxlen
        have hpos : 0 < min (B.card + 1) A.card :=
          lt_min (Nat.succ_pos _) (Finset.Nonempty.card_pos hA)
        omega))
      (interleave_nodup
        ((List.take_sublist _ _).nodup (Finset.nodup_toList A))
        (Finset.nodup_toList B)
        (fun a ha hbB ↦
          (Disjoint.notMem_left hXY (hAX (hmem _ ha)))
            (hBY (Finset.mem_toList.mp hbB))))
      (interleave_adjXY_isChain (c := .blue)
        (fun a ha b hbB ↦
          ⟨Or.inl ⟨hAX (hmem _ ha), hBY (Finset.mem_toList.mp hbB)⟩,
           hb _ (hmem _ ha) _ (Finset.mem_toList.mp hbB)⟩)
        (by simp only [List.length_take, Finset.length_toList]; omega)
        (by simp only [List.length_take, Finset.length_toList]; omega))
    refine ⟨p, hch, ?_⟩
    rw [hlen]
    simp only [interleave_length, List.length_take, Finset.length_toList,
      min_eq_right hBA]
    omega
  · -- `A.card ≤ B.card`: path starts in `Y`, first list from `B`.
    have hmem : ∀ b ∈ B.toList.take (A.card + 1), b ∈ B :=
      fun b hb' ↦ Finset.mem_toList.mp ((List.take_sublist _ _).mem hb')
    obtain ⟨p, hch, hlen⟩ := vertPath_of_chain
      (interleave_ne_nil (by
        intro hcon
        have hxlen : (B.toList.take (A.card + 1)).length = min (A.card + 1) B.card := by
          rw [List.length_take, Finset.length_toList]
        rw [hcon, List.length_nil] at hxlen
        have hpos : 0 < min (A.card + 1) B.card :=
          lt_min (Nat.succ_pos _) (Finset.Nonempty.card_pos hB)
        omega))
      (interleave_nodup
        ((List.take_sublist _ _).nodup (Finset.nodup_toList B))
        (Finset.nodup_toList A)
        (fun a ha hbA ↦
          (Disjoint.notMem_right hXY (hBY (hmem _ ha)))
            (hAX (Finset.mem_toList.mp hbA))))
      (interleave_adjXY_isChain (c := .blue)
        (fun a ha b hbA ↦
          ⟨Or.inr ⟨hBY (hmem _ ha), hAX (Finset.mem_toList.mp hbA)⟩,
           fun hAdj ↦ hb _ (Finset.mem_toList.mp hbA) _ (hmem _ ha) hAdj.symm⟩)
        (by simp only [List.length_take, Finset.length_toList]; omega)
        (by simp only [List.length_take, Finset.length_toList]; omega))
    refine ⟨p, hch, ?_⟩
    rw [hlen]
    simp only [interleave_length, List.length_take, Finset.length_toList,
      min_eq_left hge]
    omega

/-- If a bipath covers all of `X ∪ Y`, one of its branches settles the
Ramsey alternative. -/
theorem bipath_cover {A B : List V} {z : V} {k ℓ : ℕ}
    (hb : IsBipath G X Y A z B)
    (hcov : ∀ v ∈ X ∪ Y, v ∈ A ++ z :: B)
    (hn : k + ℓ ≤ (X ∪ Y).card) :
    ∃ p : VertPath V,
      (p.toList.IsChain (Color.adjXY G X Y .red) ∧ k + 1 ≤ p.toList.length) ∨
      (p.toList.IsChain (Color.adjXY G X Y .blue) ∧ ℓ + 1 ≤ p.toList.length) := by
  obtain ⟨hred, hblue, hnd⟩ := hb
  have hcard : (X ∪ Y).card ≤ (A ++ z :: B).length := by
    have hsub : (X ∪ Y) ⊆ (A ++ z :: B).toFinset :=
      fun v hv ↦ List.mem_toFinset.mpr (hcov v hv)
    calc (X ∪ Y).card ≤ (A ++ z :: B).toFinset.card := Finset.card_le_card hsub
      _ = (A ++ z :: B).length := List.toFinset_card_of_nodup hnd
  have hlen : (A ++ z :: B).length = A.length + B.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  obtain ⟨hndA, hndzB, hdis⟩ := List.nodup_append.mp hnd
  rcases Nat.lt_or_ge A.length k with hAk | hAk
  · -- red branch too short ⇒ blue branch must be long
    obtain ⟨p, hch, plen⟩ := vertPath_of_chain (List.cons_ne_nil _ _) hndzB hblue
    refine ⟨p, Or.inr ⟨hch, ?_⟩⟩
    rw [plen]
    simp only [List.length_cons]
    omega
  · -- red branch is long enough
    have hndAz : (A ++ [z]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hndA, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb
      subst a
      exact hdis _ ha _ List.mem_cons_self rfl
    obtain ⟨p, hch, plen⟩ := vertPath_of_chain (by simp) hndAz hred
    refine ⟨p, Or.inl ⟨hch, ?_⟩⟩
    rw [plen]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-!
### Either-order bipaths

Gyárfás–Lehel's extension arguments produce vertex sequences whose single
colour switch runs either red-to-blue (`IsBipath`) or blue-to-red
(`IsBipathB`).  A *maximal* either-order bipath forces the colouring into the
two-clique structure that settles the Ramsey alternative.
-/

variable {G : SimpleGraph V} {X Y : Finset V}

/-- A "blue-first" bipath: `A ++ [z]` is a blue chain, `z :: B` a red chain.
This is exactly `IsBipath` in the complement colouring `Gᶜ`. -/
def IsBipathB (G : SimpleGraph V) (X Y : Finset V) (A : List V) (z : V)
    (B : List V) : Prop :=
  (A ++ [z]).IsChain (Color.adjXY G X Y .blue) ∧
  (z :: B).IsChain (Color.adjXY G X Y .red) ∧
  (A ++ z :: B).Nodup

theorem acrossXY.ne {a b : V} (hXY : Disjoint X Y) (h : acrossXY X Y a b) :
    a ≠ b := by
  rintro rfl
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h
  · exact Disjoint.notMem_left hXY h1 h2
  · exact Disjoint.notMem_right hXY h1 h2

theorem Color.adjXY.ne {c : Color} {a b : V} (hXY : Disjoint X Y)
    (h : Color.adjXY G X Y c a b) : a ≠ b :=
  acrossXY.ne hXY (Color.adjXY.across h)

/-- `Gᶜ`-red across `X Y` is `G`-blue. -/
theorem Color.adjXY.compl_red {a b : V} (hXY : Disjoint X Y)
    (h : Color.adjXY Gᶜ X Y .red a b) : Color.adjXY G X Y .blue a b := by
  obtain ⟨hx, hadj⟩ := h
  rw [SimpleGraph.compl_adj] at hadj
  exact ⟨hx, hadj.2⟩

/-- `Gᶜ`-blue across `X Y` is `G`-red. -/
theorem Color.adjXY.compl_blue {a b : V} (hXY : Disjoint X Y)
    (h : Color.adjXY Gᶜ X Y .blue a b) : Color.adjXY G X Y .red a b := by
  obtain ⟨hx, hadj⟩ := h
  rw [SimpleGraph.compl_adj] at hadj
  push_neg at hadj
  exact ⟨hx, hadj (acrossXY.ne hXY hx)⟩

theorem IsBipath.of_compl {A : List V} {z : V} {B : List V} (hXY : Disjoint X Y)
    (h : IsBipath Gᶜ X Y A z B) : IsBipathB G X Y A z B :=
  ⟨h.1.imp fun _ _ hh ↦ Color.adjXY.compl_red hXY hh,
   h.2.1.imp fun _ _ hh ↦ Color.adjXY.compl_blue hXY hh, h.2.2⟩

theorem IsBipathB.of_compl {A : List V} {z : V} {B : List V} (hXY : Disjoint X Y)
    (h : IsBipathB Gᶜ X Y A z B) : IsBipath G X Y A z B :=
  ⟨h.1.imp fun _ _ hh ↦ Color.adjXY.compl_blue hXY hh,
   h.2.1.imp fun _ _ hh ↦ Color.adjXY.compl_red hXY hh, h.2.2⟩

/-- `G`-blue across `X Y` is `Gᶜ`-red. -/
theorem Color.adjXY.to_compl_red {a b : V} (hXY : Disjoint X Y)
    (h : Color.adjXY G X Y .blue a b) : Color.adjXY Gᶜ X Y .red a b := by
  obtain ⟨hx, hadj⟩ := h
  refine ⟨hx, ?_⟩
  rw [SimpleGraph.compl_adj]
  exact ⟨acrossXY.ne hXY hx, hadj⟩

/-- `G`-red across `X Y` is `Gᶜ`-blue. -/
theorem Color.adjXY.to_compl_blue {a b : V} (hXY : Disjoint X Y)
    (h : Color.adjXY G X Y .red a b) : Color.adjXY Gᶜ X Y .blue a b := by
  obtain ⟨hx, hadj⟩ := h
  refine ⟨hx, ?_⟩
  rw [SimpleGraph.compl_adj]
  push_neg
  exact fun _ ↦ hadj

theorem IsBipathB.to_compl {A : List V} {z : V} {B : List V} (hXY : Disjoint X Y)
    (h : IsBipathB G X Y A z B) : IsBipath Gᶜ X Y A z B :=
  ⟨h.1.imp fun _ _ hh ↦ Color.adjXY.to_compl_red hXY hh,
   h.2.1.imp fun _ _ hh ↦ Color.adjXY.to_compl_blue hXY hh, h.2.2⟩

/-- An either-order bipath: a vertex list with a single colour switch. -/
def IsBipathO (G : SimpleGraph V) (X Y : Finset V) (A : List V) (z : V)
    (B : List V) : Prop :=
  IsBipath G X Y A z B ∨ IsBipathB G X Y A z B

/-- A maximum either-order bipath exists and is red- or blue-first. -/
theorem exists_max_bipathO (G : SimpleGraph V) (X Y : Finset V)
    (hXY : Disjoint X Y) (v : V) :
    ∃ A z B, IsBipathO G X Y A z B ∧
      ∀ A' z' B', IsBipathO G X Y A' z' B' → bipathLen A' z' B' ≤ bipathLen A z B := by
  obtain ⟨A₁, z₁, B₁, h1, hmax1⟩ := exists_max_bipath G X Y v
  obtain ⟨A₂, z₂, B₂, h2, hmax2⟩ := exists_max_bipath Gᶜ X Y v
  have h2' : IsBipathB G X Y A₂ z₂ B₂ := IsBipath.of_compl hXY h2
  rcases Nat.le_or_ge (bipathLen A₂ z₂ B₂) (bipathLen A₁ z₁ B₁) with hle | hle
  · refine ⟨A₁, z₁, B₁, Or.inl h1, fun A' z' B' h ↦ ?_⟩
    rcases h with h | h
    · exact hmax1 _ _ _ h
    · have : IsBipath Gᶜ X Y A' z' B' := IsBipathB.to_compl hXY h
      exact (hmax2 _ _ _ this).trans hle
  · refine ⟨A₂, z₂, B₂, Or.inr h2', fun A' z' B' h ↦ ?_⟩
    rcases h with h | h
    · exact (hmax1 _ _ _ h).trans hle
    · have : IsBipath Gᶜ X Y A' z' B' := IsBipathB.to_compl hXY h
      exact hmax2 _ _ _ this

/-!
### Extension moves for maximal bipaths

Gyárfás–Lehel's argument exhibits, in each configuration that is *not* the
surviving type (iii), an either-order bipath strictly longer than the maximum
— a contradiction.  The two workhorse lemmas below cover case (i) (endpoints
in different classes) and case (ii) (endpoints and midpoint in one class).
-/

theorem List.head?_eq_head {l : List V} (hl : l ≠ []) :
    l.head? = some (l.head hl) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l => simp

/-- The last edge of the red branch of a nonempty bipath. -/
theorem IsBipath.red_last_edge {A : List V} {z : V} {B : List V}
    (hb : IsBipath G X Y A z B) (hA : A ≠ []) :
    Color.adjXY G X Y .red (A.getLast hA) z := by
  obtain ⟨hred, -, -⟩ := hb
  have h := List.IsChain.rel_getLast_head_of_append hred hA (by simp)
  rwa [List.head_cons] at h

/-- The first edge of the blue branch of a nonempty bipath. -/
theorem IsBipath.blue_first_edge {A : List V} {z : V} {B : List V}
    (hb : IsBipath G X Y A z B) (hB : B ≠ []) :
    Color.adjXY G X Y .blue z (B.head hB) := by
  obtain ⟨-, hblue, -⟩ := hb
  have h := List.isChain_cons.mp hblue
  exact h.1 _ (by rw [List.head?_eq_head hB]; exact Option.mem_some_iff.mpr rfl)

/-- A vertex outside the bipath is outside every piece of it. -/
theorem IsBipath.notMem_pieces {A : List V} {z : V} {B : List V}
    (hb : IsBipath G X Y A z B) {u : V} (hu : u ∉ A ++ z :: B) :
    u ∉ A ∧ u ≠ z ∧ u ∉ B := by
  refine ⟨fun h ↦ hu (List.mem_append_left _ h),
    fun h ↦ hu (List.mem_append_right _ (List.mem_cons.mpr (Or.inl h))),
    fun h ↦ hu (List.mem_append_right _ (List.mem_cons_of_mem _ h))⟩

/-- The pieces of a bipath are pairwise disjoint. -/
theorem IsBipath.disjoint_pieces {A : List V} {z : V} {B : List V}
    (hb : IsBipath G X Y A z B) :
    z ∉ A ∧ z ∉ B ∧ A.Disjoint B := by
  obtain ⟨-, -, hnd⟩ := hb
  obtain ⟨-, hndzB, hdis⟩ := List.nodup_append.mp hnd
  obtain ⟨hzB, -⟩ := List.nodup_cons.mp hndzB
  refine ⟨?_, hzB, fun a ha hb' ↦ ?_⟩
  · intro h
    exact hdis _ h _ List.mem_cons_self rfl
  · exact hdis _ ha _ (List.mem_cons_of_mem _ hb') rfl


/-- **GL case (i).**  If the endpoints `A.head`, `B.getLast` of a maximal
either-order bipath lie in different classes, then no vertex outside the
bipath lies in the midpoint's opposite class. -/
theorem bipathO_leftover_opp_of_diff_ends
    {A : List V} {z : V} {B : List V} (hXY : Disjoint X Y)
    (hb : IsBipath G X Y A z B)
    (hmax : ∀ A' z' B', IsBipathO G X Y A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B)
    {u : V} (hu : u ∉ A ++ z :: B) (hz : z ∈ X) (huY : u ∈ Y)
    (hA : A ≠ []) (hB : B ≠ [])
    (hdiff : acrossXY X Y (A.head hA) (B.getLast hB)) : False := by
  have harz := IsBipath.red_last_edge hb hA
  have hzb1 := IsBipath.blue_first_edge hb hB
  obtain ⟨hred, hblue, hnd⟩ := hb
  set a₁ := A.head hA
  set aᵣ := A.getLast hA
  set bₛ := B.getLast hB
  have huz : acrossXY X Y u z := Or.inr ⟨huY, hz⟩
  have hArev : A.reverse.IsChain (Color.adjXY G X Y .red) :=
    Color.adjXY.isChain_reverse hred.left_of_append
  have hBrev : B.reverse.IsChain (Color.adjXY G X Y .blue) :=
    Color.adjXY.isChain_reverse hblue.tail
  have hndS : (u :: A ++ z :: B).Nodup := List.nodup_cons.mpr ⟨hu, hnd⟩
  have hAl : 1 ≤ A.length := List.length_pos_of_ne_nil hA
  have hBl : 1 ≤ B.length := List.length_pos_of_ne_nil hB
  -- list identities
  have hBsnoc : B.dropLast ++ [bₛ] = B :=
    List.dropLast_append_getLast? _
      (by rw [List.getLast?_eq_getLast_of_ne_nil hB]
          exact Option.mem_some_iff.mpr rfl)
  have hBrev_eq : B.reverse = bₛ :: B.dropLast.reverse := by
    conv_lhs => rw [← hBsnoc]
    simp
  have hAcons : a₁ :: A.tail = A := List.cons_head_tail hA
  have hAtail : A.tail.reverse ++ [a₁] = A.reverse := by
    conv_rhs => rw [← hAcons, List.reverse_cons]
  -- permutations of the extended vertex list
  have hp1 : List.Perm (A ++ z :: B) (z :: A ++ B) := List.perm_middle
  have hpAB : List.Perm (A ++ B) (A.reverse ++ B.reverse) := by
    have h : List.Perm ((B ++ A).reverse) (B ++ A) := List.reverse_perm _
    rw [List.reverse_append] at h
    exact List.perm_append_comm.trans h.symm
  have hpermR : List.Perm (u :: z :: A.reverse ++ B.reverse) (u :: A ++ z :: B) :=
    ((hpAB.symm.cons z).cons u).trans (hp1.symm.cons u)
  have hpermB : List.Perm (u :: z :: B ++ A) (u :: A ++ z :: B) :=
    ((List.perm_append_comm.cons z).cons u).trans (hp1.symm.cons u)
  -- case split on the colour of `(u,z)`
  rcases Color.adjXY_cases huz with huzc | huzc
  · -- `(u,z)` red: traverse `u,z,Aᵣ,…,A₁,Bₛ,…,B₁`
    have huzArev : (u :: z :: A.reverse).IsChain (Color.adjXY G X Y .red) := by
      rw [List.isChain_cons]
      refine ⟨fun y hy ↦ ?_, ?_⟩
      · simp only [List.head?_cons, Option.mem_some_iff] at hy
        subst hy; exact huzc
      · rw [List.isChain_cons]
        refine ⟨fun y hy ↦ ?_, hArev⟩
        rw [List.head?_reverse] at hy
        obtain ⟨-, rfl⟩ := List.mem_getLast?_eq_getLast hy
        exact Color.adjXY.symm harz
    rcases Color.adjXY_cases hdiff with hJ | hJ
    · -- `(A₁,Bₛ)` red: bipath `([u,z]++A.reverse, bₛ, B.dropLast.reverse)`
      have hbp : IsBipath G X Y ([u, z] ++ A.reverse) bₛ B.dropLast.reverse := by
        refine ⟨?_, ?_, ?_⟩
        · rw [List.isChain_append]
          refine ⟨huzArev, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
          rw [List.getLast?_append_of_ne_nil _ (by simpa using hA),
            List.getLast?_reverse, List.head?_eq_head hA] at hx
          simp only [List.head?_singleton, Option.mem_some_iff] at hx hy
          subst hx; subst hy; exact hJ
        · rw [← hBrev_eq]; exact hBrev
        · have hT : ([u, z] ++ A.reverse) ++ bₛ :: B.dropLast.reverse =
              u :: z :: A.reverse ++ B.reverse := by
            rw [← hBrev_eq]; simp
          rw [hT]; exact (hpermR.nodup_iff).mpr hndS
      exact absurd (hmax _ _ _ (Or.inl hbp)) (by simp [bipathLen]; omega)
    · -- `(A₁,Bₛ)` blue: bipath `([u,z]++A.tail.reverse, a₁, B.reverse)`
      have hbp : IsBipath G X Y ([u, z] ++ A.tail.reverse) a₁ B.reverse := by
        refine ⟨?_, ?_, ?_⟩
        · have : ([u, z] ++ A.tail.reverse) ++ [a₁] =
              [u, z] ++ A.reverse := by
            rw [List.append_assoc, hAtail]
          rw [this]; exact huzArev
        · rw [List.isChain_cons]
          refine ⟨fun y hy ↦ ?_, hBrev⟩
          rw [List.head?_reverse, List.getLast?_eq_getLast_of_ne_nil hB] at hy
          simp only [Option.mem_some_iff] at hy; subst hy
          exact hJ
        · have hT : ([u, z] ++ A.tail.reverse) ++ a₁ :: B.reverse =
              u :: z :: A.reverse ++ B.reverse := by
            rw [List.append_assoc, List.append_cons, hAtail]
            rfl
          rw [hT]; exact (hpermR.nodup_iff).mpr hndS
      exact absurd (hmax _ _ _ (Or.inl hbp)) (by simp [bipathLen]; omega)
  · -- `(u,z)` blue: traverse `u,z,B₁,…,Bₛ,A₁,…,Aᵣ` (blue-first)
    have huzB : (u :: z :: B).IsChain (Color.adjXY G X Y .blue) := by
      rw [List.isChain_cons]
      refine ⟨fun y hy ↦ ?_, ?_⟩
      · simp only [List.head?_cons, Option.mem_some_iff] at hy
        subst hy; exact huzc
      · rw [List.isChain_cons]
        refine ⟨fun y hy ↦ ?_, hblue.tail⟩
        rw [List.head?_eq_head hB] at hy
        simp only [Option.mem_some_iff] at hy; subst hy
        exact hzb1
    rcases Color.adjXY_cases (acrossXY.symm hdiff) with hJ | hJ
    · -- `(Bₛ,A₁)` red: blue-first bipath `([u,z]++B.dropLast, bₛ, A)`
      have hbp : IsBipathB G X Y ([u, z] ++ B.dropLast) bₛ A := by
        refine ⟨?_, ?_, ?_⟩
        · have : ([u, z] ++ B.dropLast) ++ [bₛ] = [u, z] ++ B := by
            rw [List.append_assoc, hBsnoc]
          rw [this]; exact huzB
        · rw [List.isChain_cons]
          refine ⟨fun y hy ↦ ?_, hred.left_of_append⟩
          rw [List.head?_eq_head hA] at hy
          simp only [Option.mem_some_iff] at hy; subst hy; exact hJ
        · have hT : ([u, z] ++ B.dropLast) ++ bₛ :: A =
              u :: z :: B ++ A := by
            rw [List.append_assoc, List.append_cons, hBsnoc]
            rfl
          rw [hT]; exact (hpermB.nodup_iff).mpr hndS
      exact absurd (hmax _ _ _ (Or.inr hbp)) (by simp [bipathLen]; omega)
    · -- `(Bₛ,A₁)` blue: blue-first bipath `([u,z]++B, a₁, A.tail)`
      have hbp : IsBipathB G X Y ([u, z] ++ B) a₁ A.tail := by
        refine ⟨?_, ?_, ?_⟩
        · rw [List.isChain_append]
          refine ⟨huzB, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
          rw [List.getLast?_append_of_ne_nil _ hB,
            List.getLast?_eq_getLast_of_ne_nil hB] at hx
          simp only [List.head?_singleton, Option.mem_some_iff] at hx hy
          subst hx; subst hy; exact hJ
        · rw [hAcons]; exact hred.left_of_append
        · have hT : ([u, z] ++ B) ++ a₁ :: A.tail =
              u :: z :: B ++ A := by
            rw [List.append_assoc, hAcons]
            rfl
          rw [hT]; exact (hpermB.nodup_iff).mpr hndS
      exact absurd (hmax _ _ _ (Or.inr hbp)) (by simp [bipathLen]; omega)

/-- **GL case (ii).**  If the endpoints `A.head`, `B.getLast` and the midpoint
`z` of a maximal either-order bipath all lie in the same class, then no vertex
outside the bipath lies in the opposite class: any such vertex `u` extends the
bipath, contradicting maximality. -/
theorem bipathO_leftover_opp_of_same_ends
    {A : List V} {z : V} {B : List V} (hXY : Disjoint X Y)
    (hb : IsBipath G X Y A z B)
    (hmax : ∀ A' z' B', IsBipathO G X Y A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B)
    {u : V} (hu : u ∉ A ++ z :: B) (hz : z ∈ X) (huY : u ∈ Y)
    (hA : A ≠ []) (hB : B ≠ [])
    (haX : A.head hA ∈ X) (hbX : B.getLast hB ∈ X) : False := by
  have hzb1 := IsBipath.blue_first_edge hb hB
  have harz := IsBipath.red_last_edge hb hA
  obtain ⟨hred, hblue, hnd⟩ := hb
  set a₁ := A.head hA
  set bₛ := B.getLast hB
  have hndS : (u :: A ++ z :: B).Nodup := List.nodup_cons.mpr ⟨hu, hnd⟩
  have hAl : 1 ≤ A.length := List.length_pos_of_ne_nil hA
  have hBl : 1 ≤ B.length := List.length_pos_of_ne_nil hB
  have hBsnoc : B.dropLast ++ [bₛ] = B :=
    List.dropLast_append_getLast? _
      (by rw [List.getLast?_eq_getLast_of_ne_nil hB]
          exact Option.mem_some_iff.mpr rfl)
  have hBrev_eq : B.reverse = bₛ :: B.dropLast.reverse := by
    conv_lhs => rw [← hBsnoc]
    simp
  have hAcons : a₁ :: A.tail = A := List.cons_head_tail hA
  have hBrev : B.reverse.IsChain (Color.adjXY G X Y .blue) :=
    Color.adjXY.isChain_reverse hblue.tail
  have huz : acrossXY X Y u z := Or.inr ⟨huY, hz⟩
  -- the `u–a₁` edge cannot be red: else `(u::A, z, B)` is longer
  rcases Color.adjXY_cases (show acrossXY X Y u a₁ from Or.inr ⟨huY, haX⟩)
    with hua | hua
  · have hbp : IsBipath G X Y (u :: A) z B := by
      refine ⟨?_, hblue, ?_⟩
      · rw [List.cons_append, List.isChain_cons]
        refine ⟨fun y hy ↦ ?_, hred⟩
        rw [List.head?_append_of_ne_nil _ hA, List.head?_eq_head hA] at hy
        simp only [Option.mem_some_iff] at hy; subst hy
        exact hua
      · exact hndS
    exact absurd (hmax _ _ _ (Or.inl hbp)) (by simp [bipathLen] <;> omega)
  · -- `u–a₁` is blue.  If `u–bₛ` is blue, `(A, z, B++[u])` is longer.
    rcases Color.adjXY_cases (show acrossXY X Y u bₛ from Or.inr ⟨huY, hbX⟩)
      with hub | hub
    · -- `u–bₛ` red: the colour of `u–z` decides the splice
      rcases Color.adjXY_cases huz with huzc | huzc
      · -- `u–z` red: bipath `(A++[z,u], bₛ, B.dropLast.reverse)`
        have hbp : IsBipath G X Y (A ++ [z, u]) bₛ B.dropLast.reverse := by
          refine ⟨?_, ?_, ?_⟩
          · rw [List.isChain_append]
            refine ⟨?_, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
            · rw [List.isChain_append]
              refine ⟨(List.isChain_append.mp hred).1, ?_, fun x hx y hy ↦ ?_⟩
              · rw [List.isChain_cons]
                refine ⟨fun y hy ↦ ?_, List.isChain_singleton _⟩
                simp only [List.head?_cons, Option.mem_some_iff] at hy
                subst hy; exact Color.adjXY.symm huzc
              · simp only [List.head?_cons, Option.mem_some_iff] at hy
                subst hy
                obtain ⟨_, rfl⟩ := List.mem_getLast?_eq_getLast hx
                exact harz
            · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
                List.getLast?_cons_cons, List.getLast?_singleton] at hx
              simp only [List.head?_singleton, Option.mem_some_iff] at hx hy
              subst hx; subst hy; exact hub
          · rw [← hBrev_eq]; exact hBrev
          · have hT : (A ++ [z, u]) ++ bₛ :: B.dropLast.reverse =
                A ++ z :: u :: B.reverse := by
              rw [List.append_assoc, ← hBrev_eq]
              rfl
            rw [hT]
            have hp : List.Perm (A ++ z :: u :: B.reverse)
                (u :: A ++ z :: B) :=
              (List.perm_middle.trans (List.perm_middle.cons z)).trans <|
                (List.Perm.swap u z _).trans <|
                  ((((List.reverse_perm B).append_left A).cons z).cons u).trans
                    (List.perm_middle.symm.cons u)
            exact hp.nodup_iff.mpr hndS
        exact absurd (hmax _ _ _ (Or.inl hbp)) (by simp [bipathLen] <;> omega)
      · -- `u–z` blue: blue-first bipath `(B.reverse++[z,u], a₁, A.tail)`
        have hbp : IsBipathB G X Y (B.reverse ++ [z, u]) a₁ A.tail := by
          refine ⟨?_, ?_, ?_⟩
          · rw [List.isChain_append]
            refine ⟨?_, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
            · rw [List.isChain_append]
              refine ⟨hBrev, ?_, fun x hx y hy ↦ ?_⟩
              · rw [List.isChain_cons]
                refine ⟨fun y hy ↦ ?_, List.isChain_singleton _⟩
                simp only [List.head?_cons, Option.mem_some_iff] at hy
                subst hy; exact Color.adjXY.symm huzc
              · rw [List.getLast?_reverse, List.head?_eq_head hB] at hx
                simp only [List.head?_cons, Option.mem_some_iff] at hx hy
                subst hx; subst hy
                exact Color.adjXY.symm hzb1
            · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
                List.getLast?_cons_cons, List.getLast?_singleton] at hx
              simp only [List.head?_singleton, Option.mem_some_iff] at hx hy
              subst hx; subst hy; exact hua
          · rw [hAcons]; exact (List.isChain_append.mp hred).1
          · have hT : (B.reverse ++ [z, u]) ++ a₁ :: A.tail =
                B.reverse ++ z :: u :: A := by
              rw [List.append_assoc, hAcons]
              rfl
            rw [hT]
            have hp : List.Perm (B.reverse ++ z :: u :: A)
                (u :: A ++ z :: B) :=
              (List.perm_middle.trans (List.perm_middle.cons z)).trans <|
                (List.Perm.swap u z _).trans <|
                  (((List.perm_append_comm.trans
                    ((List.reverse_perm B).append_left A)).cons z).cons u).trans
                    (List.perm_middle.symm.cons u)
            exact hp.nodup_iff.mpr hndS
        exact absurd (hmax _ _ _ (Or.inr hbp)) (by simp [bipathLen] <;> omega)
    · -- `u–bₛ` blue: bipath `(A, z, B++[u])` is longer
      have hbp : IsBipath G X Y A z (B ++ [u]) := by
        refine ⟨hred, ?_, ?_⟩
        · rw [List.isChain_cons]
          refine ⟨fun y hy ↦ ?_, ?_⟩
          · rw [List.head?_append_of_ne_nil _ hB, List.head?_eq_head hB] at hy
            simp only [Option.mem_some_iff] at hy; subst hy
            exact hzb1
          · rw [List.isChain_append]
            refine ⟨hblue.tail, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
            simp only [List.head?_singleton, Option.mem_some_iff] at hy
            subst hy
            obtain ⟨_, rfl⟩ := List.mem_getLast?_eq_getLast hx
            exact Color.adjXY.symm hub
        · have hp : List.Perm (A ++ z :: (B ++ [u])) (u :: A ++ z :: B) :=
            (List.perm_middle (l₁ := A) (l₂ := B ++ [u]) (a := z)).trans <|
              ((List.Perm.of_eq (List.append_assoc A B [u]).symm).cons z).trans <|
                (List.perm_append_comm.cons z).trans <|
                  (List.Perm.swap u z _).trans
                    ((List.perm_middle (l₁ := A) (l₂ := B) (a := z)).symm.cons u)
          exact hp.nodup_iff.mpr hndS
      exact absurd (hmax _ _ _ (Or.inl hbp)) (by simp [bipathLen] <;> omega)

/-- **GL claim A (i).**  For a maximal either-order bipath of type (iii) —
endpoints in the same class, midpoint `z` in the other class — the edge from
the first endpoint `A.head` to the midpoint is red.  Otherwise rotating the
bipath yields a type-(i) or type-(ii) maximal bipath, both impossible while a
vertex outside the bipath lies in `z`'s class. -/
theorem bipathO_red_head_mid_of_type3
    {A : List V} {z : V} {B : List V} (hXY : Disjoint X Y)
    (hb : IsBipath G X Y A z B)
    (hmax : ∀ A' z' B', IsBipathO G X Y A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B)
    {u : V} (hu : u ∉ A ++ z :: B) (huY : u ∈ Y)
    (hA : A ≠ []) (hB : B ≠ [])
    (haX : A.head hA ∈ X) (hbX : B.getLast hB ∈ X) (hz : z ∈ Y) :
    Color.adjXY G X Y .red (A.head hA) z := by
  have harz := IsBipath.red_last_edge hb hA
  obtain ⟨hred, hblue, hnd⟩ := hb
  set a₁ := A.head hA
  have huz : acrossXY X Y u a₁ := Or.inr ⟨huY, haX⟩
  rcases Color.adjXY_cases (show acrossXY X Y a₁ z from Or.inl ⟨haX, hz⟩)
    with haz | haz
  · exact haz
  · -- `a₁–z` blue: the rotated bipath `S' = (A.tail.reverse, a₁, z::B)`
    -- has the same length, hence is maximal too.
    exfalso
    have hAl : 1 ≤ A.length := List.length_pos_of_ne_nil hA
    have hArev : A.reverse.IsChain (Color.adjXY G X Y .red) :=
      Color.adjXY.isChain_reverse hred.left_of_append
    have hAtail : A.tail.reverse ++ [a₁] = A.reverse := by
      conv_rhs => rw [← List.cons_head_tail hA, List.reverse_cons]
    have hp : List.Perm (A.tail.reverse ++ a₁ :: z :: B) (A ++ z :: B) := by
      have h1 : List.Perm (A.tail.reverse ++ a₁ :: z :: B)
          ((A.tail.reverse ++ [a₁]) ++ z :: B) :=
        (List.append_assoc _ _ _).symm ▸ List.Perm.refl _
      rw [hAtail] at h1
      exact h1.trans ((List.reverse_perm A).append_right _)
    have hbS' : IsBipath G X Y A.tail.reverse a₁ (z :: B) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hAtail]; exact hArev
      · rw [List.isChain_cons]
        refine ⟨fun y hy ↦ ?_, hblue⟩
        simp only [List.head?_cons, Option.mem_some_iff] at hy
        subst hy; exact haz
      · exact hp.nodup_iff.mpr hnd
    have hlenS' : bipathLen A.tail.reverse a₁ (z :: B) = bipathLen A z B := by
      simp [bipathLen]; omega
    have hmax' := hlenS'.symm ▸ hmax
    by_cases hAt : A.tail = []
    · -- `r = 1`, so `A = [a₁]` and `S = a₁ :: z :: B`: `u–a₁` extends directly
      have hA2 : A = [a₁] := by
        have h := List.cons_head_tail hA; rw [hAt] at h; exact h.symm
      rw [hA2] at hu hnd
      rcases Color.adjXY_cases huz with hua | hua
      · -- `u–a₁` red: bipath `([u], a₁, z::B)` is longer
        have hbp : IsBipath G X Y [u] a₁ (z :: B) := by
          refine ⟨?_, ?_, ?_⟩
          · rw [List.isChain_append]
            refine ⟨List.isChain_singleton _, List.isChain_singleton _,
              fun x hx y hy ↦ ?_⟩
            simp only [List.getLast?_singleton, List.head?_singleton,
              Option.mem_some_iff] at hx hy
            subst hx; subst hy; exact hua
          · rw [List.isChain_cons]
            refine ⟨fun y hy ↦ ?_, hblue⟩
            simp only [List.head?_cons, Option.mem_some_iff] at hy
            subst hy; exact haz
          · exact List.nodup_cons.mpr ⟨hu, hnd⟩
        exact absurd (hmax _ _ _ (Or.inl hbp))
          (by simp [bipathLen, hA2] <;> omega)
      · -- `u–a₁` blue: bipath `([], u, a₁::z::B)` is longer
        have hbp : IsBipath G X Y [] u (a₁ :: z :: B) := by
          refine ⟨List.isChain_singleton _, ?_, ?_⟩
          · rw [List.isChain_cons]
            refine ⟨fun y hy ↦ ?_, ?_⟩
            · simp only [List.head?_cons, Option.mem_some_iff] at hy
              subst hy; exact hua
            · rw [List.isChain_cons]
              refine ⟨fun y hy ↦ ?_, hblue⟩
              simp only [List.head?_cons, Option.mem_some_iff] at hy
              subst hy; exact haz
          · exact List.nodup_cons.mpr ⟨hu, hnd⟩
        exact absurd (hmax _ _ _ (Or.inl hbp))
          (by simp [bipathLen, hA2] <;> omega)
    · -- `r ≥ 2`: `S'` has a genuine first endpoint `aᵣ = A.getLast`
      have hAtr : A.tail.reverse ≠ [] := by
        rwa [List.reverse_ne_nil_iff]
      have hhead? : (A.tail.reverse).head? = some (A.getLast hA) := by
        rw [List.head?_reverse, ← List.getLast?_cons_of_ne_nil hAt,
          List.cons_head_tail hA, List.getLast?_eq_getLast_of_ne_nil hA]
      have hhead : (A.tail.reverse).head hAtr = A.getLast hA :=
        Option.some.inj (List.head?_eq_head hAtr ▸ hhead?)
      have hgl : (z :: B).getLast (List.cons_ne_nil _ _) = B.getLast hB :=
        List.getLast_cons hB
      -- `aᵣ ∈ X` since `aᵣ–z` is an edge and `z ∈ Y`
      have haᵣ : A.getLast hA ∈ X :=
        (Color.adjXY.left_mem_iff hXY harz).mpr hz
      -- `u` is also outside `S'`, whose vertex list is a perm of `S`'s
      have hu' : u ∉ A.tail.reverse ++ a₁ :: z :: B :=
        fun h ↦ hu (hp.mem_iff.mp h)
      -- type (ii): `aᵣ, bₛ` and midpoint `a₁` all in `X`
      exact bipathO_leftover_opp_of_same_ends hXY hbS' hmax' hu' haX huY
        hAtr (List.cons_ne_nil _ _) (hhead ▸ haᵣ) (hgl ▸ hbX)

/-- **GL claim A (ii).**  For a maximal either-order bipath of type (iii) —
endpoints in the same class, midpoint `z` in the other class — the edge from
the midpoint `z` to the last endpoint `B.getLast` is blue.  Otherwise rotating
the bipath yields a type-(ii) maximal bipath. -/
theorem bipathO_blue_mid_getLast_of_type3
    {A : List V} {z : V} {B : List V} (hXY : Disjoint X Y)
    (hb : IsBipath G X Y A z B)
    (hmax : ∀ A' z' B', IsBipathO G X Y A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B)
    {u : V} (hu : u ∉ A ++ z :: B) (huY : u ∈ Y)
    (hA : A ≠ []) (hB : B ≠ [])
    (haX : A.head hA ∈ X) (hbX : B.getLast hB ∈ X) (hz : z ∈ Y) :
    Color.adjXY G X Y .blue z (B.getLast hB) := by
  have hzb1 := IsBipath.blue_first_edge hb hB
  obtain ⟨hred, hblue, hnd⟩ := hb
  set bₛ := B.getLast hB
  have hBl : 1 ≤ B.length := List.length_pos_of_ne_nil hB
  have hBsnoc : B.dropLast ++ [bₛ] = B :=
    List.dropLast_append_getLast? _
      (by rw [List.getLast?_eq_getLast_of_ne_nil hB]
          exact Option.mem_some_iff.mpr rfl)
  have hBrev_eq : B.reverse = bₛ :: B.dropLast.reverse := by
    conv_lhs => rw [← hBsnoc]
    simp
  have hBrev : B.reverse.IsChain (Color.adjXY G X Y .blue) :=
    Color.adjXY.isChain_reverse hblue.tail
  rcases Color.adjXY_cases (show acrossXY X Y z bₛ from Or.inr ⟨hz, hbX⟩)
    with hzb | hzb
  · -- `z–bₛ` red: `S'' = (A++[z], bₛ, B.dropLast.reverse)` is maximal too
    exfalso
    have hp : List.Perm ((A ++ [z]) ++ bₛ :: B.dropLast.reverse)
        (A ++ z :: B) := by
      have hT : (A ++ [z]) ++ bₛ :: B.dropLast.reverse =
          (A ++ [z]) ++ B.reverse := by rw [← hBrev_eq]
      rw [hT]
      exact (List.Perm.of_eq (List.append_assoc A [z] B.reverse)).trans
        (((List.reverse_perm B).cons z).append_left A)
    have hbS'' : IsBipath G X Y (A ++ [z]) bₛ B.dropLast.reverse := by
      refine ⟨?_, ?_, ?_⟩
      · rw [List.isChain_append]
        refine ⟨hred, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
          List.getLast?_singleton] at hx
        simp only [List.head?_singleton, Option.mem_some_iff] at hx hy
        subst hx; subst hy; exact hzb
      · rw [← hBrev_eq]; exact hBrev
      · exact hp.nodup_iff.mpr hnd
    have hlenS'' : bipathLen (A ++ [z]) bₛ B.dropLast.reverse =
        bipathLen A z B := by
      simp [bipathLen]; omega
    have hmax' := hlenS''.symm ▸ hmax
    have hu' : u ∉ (A ++ [z]) ++ bₛ :: B.dropLast.reverse :=
      fun h ↦ hu (hp.mem_iff.mp h)
    have hb1 : B.head hB ∈ X := (Color.adjXY.right_mem_iff hXY hzb1).mp hz
    by_cases hBd : B.dropLast = []
    · -- `s = 1`: `B = [b₁] = [bₛ]`; the edge `u–b₁` extends `S` directly
      have hBlen : B.length = 1 := by
        have h4 := List.length_dropLast (xs := B)
        rw [hBd] at h4
        simp only [List.length_nil] at h4; omega
      have htl : B.tail = [] := by
        apply List.eq_nil_of_length_eq_zero
        have h5 := List.length_tail (l := B)
        omega
      have e1 : B.getLast? = some (B.head hB) := by
        conv_lhs => rw [← List.cons_head_tail hB]
        rw [htl, List.getLast?_singleton]
      have hBgl : B.getLast hB = B.head hB :=
        Option.some.inj ((List.getLast?_eq_getLast_of_ne_nil hB).symm.trans e1)
      have hbs : bₛ = B.head hB := hBgl
      have hzb' : Color.adjXY G X Y .red z (B.head hB) := hbs ▸ hzb
      obtain ⟨hchA, -, hjoint⟩ := List.isChain_append.mp hred
      rw [show B = [B.head hB] from
        (by have h := List.cons_head_tail hB; rw [htl] at h; exact h.symm)]
        at hnd hu
      rcases Color.adjXY_cases
          (show acrossXY X Y u (B.head hB) from Or.inr ⟨huY, hb1⟩)
        with hub1 | hub1
      · -- `u–b₁` red: `A, z, b₁, u` is entirely red
        have hbp : IsBipath G X Y (A ++ [z, B.head hB]) u [] := by
          refine ⟨?_, List.isChain_singleton _, ?_⟩
          · rw [List.isChain_append]
            refine ⟨?_, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
            · rw [List.isChain_append]
              refine ⟨hchA, ?_, fun x hx y hy ↦ ?_⟩
              · rw [List.isChain_cons]
                refine ⟨fun y hy ↦ ?_, List.isChain_singleton _⟩
                simp only [List.head?_singleton, Option.mem_some_iff] at hy
                subst hy; exact hzb'
              · simp only [List.head?_cons, Option.mem_some_iff] at hy
                subst hy; exact hjoint x hx z (by simp)
            · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
                List.getLast?_cons_cons, List.getLast?_singleton] at hx
              simp only [List.head?_singleton, Option.mem_some_iff] at hx hy
              subst hx; subst hy; exact Color.adjXY.symm hub1
          · have hp2 : List.Perm ((A ++ [z, B.head hB]) ++ [u])
                (u :: A ++ z :: [B.head hB]) := List.perm_append_comm
            exact hp2.nodup_iff.mpr (List.nodup_cons.mpr ⟨hu, hnd⟩)
        exact absurd (hmax _ _ _ (Or.inl hbp)) (by
          simp only [bipathLen, hBlen, List.length_append, List.length_cons,
            List.length_nil]
          omega)
      · -- `u–b₁` blue: `(A++[z], b₁, [u])` is longer
        have hbp : IsBipath G X Y (A ++ [z]) (B.head hB) [u] := by
          refine ⟨?_, ?_, ?_⟩
          · rw [List.isChain_append]
            refine ⟨hred, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
            rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
              List.getLast?_singleton] at hx
            simp only [List.head?_singleton, Option.mem_some_iff] at hx hy
            subst hx; subst hy; exact hzb'
          · rw [List.isChain_cons]
            refine ⟨fun y hy ↦ ?_, List.isChain_singleton _⟩
            simp only [List.head?_singleton, Option.mem_some_iff] at hy
            subst hy; exact Color.adjXY.symm hub1
          · have s4 : List.Perm (B.head hB :: A ++ [z]) (A ++ z :: [B.head hB]) :=
              List.perm_middle.symm.trans
                ((List.Perm.swap z (B.head hB) []).append_left A)
            have hp2 : List.Perm ((A ++ [z]) ++ B.head hB :: [u])
                (u :: A ++ z :: [B.head hB]) :=
              List.perm_middle.trans <|
                (List.perm_append_comm.cons _).trans <|
                  (List.Perm.swap u (B.head hB) _).trans (s4.cons _)
            exact hp2.nodup_iff.mpr (List.nodup_cons.mpr ⟨hu, hnd⟩)
        exact absurd (hmax _ _ _ (Or.inl hbp)) (by
          simp only [bipathLen, hBlen, List.length_append, List.length_cons,
            List.length_nil]
          omega)
    · -- `s ≥ 2`: `S''` is a type-(ii) maximal bipath
      have hAz : A ++ [z] ≠ [] :=
        fun h ↦ absurd (List.append_eq_nil_iff.mp h).2 (List.cons_ne_nil _ _)
      have hBdr : B.dropLast.reverse ≠ [] := by rwa [List.reverse_ne_nil_iff]
      have hgl : (B.dropLast.reverse).getLast hBdr = B.head hB :=
        (List.getLast_reverse hBdr).trans (List.head_dropLast _)
      have hhd? : (A ++ [z]).head? = some (A.head hA) := by
        rw [List.head?_append_of_ne_nil _ hA, List.head?_eq_head hA]
      have hhd : (A ++ [z]).head hAz = A.head hA := by
        have e := List.head?_eq_head hAz
        rw [hhd?] at e
        exact (Option.some.inj e).symm
      have hend1 : (A ++ [z]).head hAz ∈ X := by rw [hhd]; exact haX
      have hend2 : (B.dropLast.reverse).getLast hBdr ∈ X := by rw [hgl]; exact hb1
      exact bipathO_leftover_opp_of_same_ends hXY hbS'' hmax' hu' hbX huY
        hAz hBdr hend1 hend2
  · exact hzb

end bip_ramsey_path

/-- **Gyárfás–Lehel 1973** (PVW24 Lemma 2.1).  For distinct `k ℓ`, every
red–blue edge colouring of the complete bipartite graph
`K_{⌈(k+ℓ)/2⌉,⌈(k+ℓ)/2⌉}` contains a red path on `k+1` vertices or a blue
path on `ℓ+1` vertices. -/
theorem bip_ramsey_path (G : SimpleGraph V) (X Y : Finset V)
    (hXY : Disjoint X Y) {k ℓ : ℕ} (hkl : k ≠ ℓ)
    (hX : X.card = (k + ℓ + 1) / 2) (hY : Y.card = (k + ℓ + 1) / 2) :
    ∃ p : VertPath V,
      (p.toList.IsChain (Color.adjXY G X Y .red) ∧ k + 1 ≤ p.toList.length) ∨
      (p.toList.IsChain (Color.adjXY G X Y .blue) ∧ ℓ + 1 ≤ p.toList.length) := by
  sorry


end JSP415
