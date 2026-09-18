import JSP415.Defs

/-!
# Gerencsér–Gyárfás 1967 (PVW24 Theorem 1.1)

Every 2-edge-coloured complete graph can be covered by two monochromatic
paths (of possibly different colours).

## Note on nonemptiness

`VertPath` requires a nonempty vertex list, so both theorems below are stated
for nonempty vertex types (`[Nonempty V]`); at `V = Fin 0` the statements
would be false since no `VertPath (Fin 0)` exists.
-/

namespace JSP415

open Finset List

section Helpers

variable {W : Type*}

/-- Append a single vertex to a chain: if `l` is a chain and its last vertex
is `R`-related to `a`, then `l ++ [a]` is a chain. -/
private theorem isChain_concat {R : W → W → Prop} {l : List W} (hl : l ≠ [])
    (hc : l.IsChain R) {a : W} (h : R (l.getLast hl) a) :
    (l ++ [a]).IsChain R := by
  rw [List.isChain_append]
  refine ⟨hc, List.isChain_singleton a, fun x hx y hy => ?_⟩
  rw [List.getLast?_eq_getLast_of_ne_nil hl, Option.mem_some] at hx
  rw [List.head?_cons, Option.mem_some] at hy
  rw [← hx, ← hy]
  exact h

/-- Append two vertices to a chain. -/
private theorem isChain_concat_pair {R : W → W → Prop} {l : List W} (hl : l ≠ [])
    (hc : l.IsChain R) {x a : W} (h1 : R (l.getLast hl) x) (h2 : R x a) :
    (l ++ [x, a]).IsChain R := by
  rw [List.isChain_append]
  refine ⟨hc, List.isChain_pair.mpr h2, fun y hy z hz => ?_⟩
  rw [List.getLast?_eq_getLast_of_ne_nil hl, Option.mem_some] at hy
  rw [List.head?_cons, Option.mem_some] at hz
  rw [← hy, ← hz]
  exact h1

/-- Nodup for `l ++ [a]` when `a` is fresh. -/
private theorem nodup_concat {l : List W} (hl : l.Nodup) {a : W} (ha : a ∉ l) :
    (l ++ [a]).Nodup := by
  rw [List.nodup_append]
  refine ⟨hl, List.nodup_singleton a, fun x hx y hy => ?_⟩
  rw [List.mem_singleton] at hy
  subst hy
  exact fun h => ha (h ▸ hx)

/-- Nodup for `l ++ [x, a]` when `x`, `a` are fresh and distinct. -/
private theorem nodup_concat_pair {l : List W} (hl : l.Nodup) {x a : W}
    (hx : x ∉ l) (ha : a ∉ l) (hxa : x ≠ a) :
    (l ++ [x, a]).Nodup := by
  rw [List.nodup_append]
  refine ⟨hl, ?_, fun y hy z hz => ?_⟩
  · rw [List.nodup_cons]
    exact ⟨fun h => hxa (List.mem_singleton.mp h), List.nodup_singleton a⟩
  · rw [List.mem_cons, List.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact fun h => hx (h ▸ hy)
    · exact fun h => ha (h ▸ hy)

/-- Membership in a nonempty list splits at the last element. -/
private theorem mem_iff_mem_dropLast {l : List W} (hl : l ≠ []) {v : W} :
    v ∈ l ↔ v ∈ l.dropLast ∨ v = l.getLast hl := by
  conv_lhs => rw [← List.dropLast_append_getLast hl]
  rw [List.mem_append, List.mem_singleton]

/-- In a nodup list the last element does not occur earlier. -/
private theorem getLast_notMem_dropLast {l : List W} (hl : l ≠ []) (hn : l.Nodup) :
    l.getLast hl ∉ l.dropLast := by
  have h1 : (l.dropLast ++ [l.getLast hl]).Nodup := by
    rw [List.dropLast_append_getLast hl]
    exact hn
  rw [List.nodup_append] at h1
  intro hmem
  exact h1.2.2 _ hmem _ (List.mem_singleton_self _) rfl

/-- Membership passes from `l.dropLast` to `l`. -/
private theorem mem_of_mem_dropLast {l : List W} {v : W} (h : v ∈ l.dropLast) :
    v ∈ l :=
  List.Sublist.mem h (List.dropLast_prefix _).sublist

/-- A list of length 1 equals the singleton of its last element. -/
private theorem eq_singleton_of_length_lt_two {l : List W} (hl : l ≠ [])
    (h : l.length < 2) : l = [l.getLast hl] := by
  have hd : l.dropLast = [] := List.dropLast_eq_nil_iff.mpr (by omega)
  have h2 := List.dropLast_append_getLast hl
  rw [hd, List.nil_append] at h2
  exact h2.symm

end Helpers

variable {W : Type*} [DecidableEq W]

/-- **Extension step**: given a red path `P` and a blue path `Q` partitioning
the finset `t`, and a fresh vertex `a ∉ t`, produce a red path and a blue
path partitioning `insert a t`.  This is the classical inductive argument for
Gerencsér–Gyárfás. -/
private theorem extend_partition (G : SimpleGraph W) {t : Finset W} {a : W}
    (ha : a ∉ t) {P Q : VertPath W}
    (hP : P.IsMonochromatic G .red) (hQ : Q.IsMonochromatic G .blue)
    (hcov : ∀ v, (v ∈ P ∨ v ∈ Q) ↔ v ∈ t) (hd : ∀ v, ¬ (v ∈ P ∧ v ∈ Q)) :
    ∃ P' Q' : VertPath W,
      P'.IsMonochromatic G .red ∧ Q'.IsMonochromatic G .blue ∧
      (∀ v, (v ∈ P' ∨ v ∈ Q') ↔ v ∈ insert a t) ∧
      (∀ v, ¬ (v ∈ P' ∧ v ∈ Q')) := by
  classical
  have hPne : P.toList ≠ [] := P.nonempty
  have hQne : Q.toList ≠ [] := Q.nonempty
  have hcovL : ∀ v, (v ∈ P.toList ∨ v ∈ Q.toList) ↔ v ∈ t := fun v => hcov v
  have hsubP : ∀ v ∈ P.toList, v ∈ t := fun v hv => (hcovL v).mp (Or.inl hv)
  have hsubQ : ∀ v ∈ Q.toList, v ∈ t := fun v hv => (hcovL v).mp (Or.inr hv)
  have haP : a ∉ P.toList := fun h => ha (hsubP a h)
  have haQ : a ∉ Q.toList := fun h => ha (hsubQ a h)
  set pk := P.toList.getLast hPne with hpk
  set qk := Q.toList.getLast hQne with hqk
  have hpkP : pk ∈ P.toList := List.getLast_mem _
  have hqkQ : qk ∈ Q.toList := List.getLast_mem _
  have hpkQ : pk ∉ Q.toList := fun h => hd pk ⟨hpkP, h⟩
  have hqkP : qk ∉ P.toList := fun h => hd qk ⟨h, hqkQ⟩
  have hpka : pk ≠ a := fun h => haP (h ▸ hpkP)
  have hqka : qk ≠ a := fun h => haQ (h ▸ hqkQ)
  have hpkqk : pk ≠ qk := fun h => hd qk ⟨h ▸ hpkP, hqkQ⟩
  by_cases h1 : G.Adj a pk
  · -- `a–pk` is red: append `a` to the red path.
    refine ⟨⟨P.toList ++ [a], by simp, nodup_concat P.nodup haP⟩, Q, ?_, hQ, ?_, ?_⟩
    · exact isChain_concat hPne hP h1.symm
    · intro v
      show (v ∈ P.toList ++ [a] ∨ v ∈ Q.toList) ↔ v ∈ insert a t
      rw [List.mem_append, List.mem_singleton, Finset.mem_insert, ← hcovL v]
      tauto
    · intro v hv
      obtain ⟨hv1, hv2⟩ := hv
      have hv1' : v ∈ P.toList ++ [a] := hv1
      have hv2' : v ∈ Q.toList := hv2
      rw [List.mem_append, List.mem_singleton] at hv1'
      rcases hv1' with h | rfl
      · exact hd v ⟨h, hv2'⟩
      · exact haQ hv2'
  · -- `a–pk` is blue.
    have hadjk : Color.adj G .blue a pk := ⟨Ne.symm hpka, h1⟩
    by_cases h2 : G.Adj a qk
    · -- `a–qk` is red; decide `pk–qk`.
      by_cases h3 : G.Adj pk qk
      · -- `pk–qk` is red: move `qk` (and then `a`) onto the red path.
        rcases Nat.lt_or_ge Q.toList.length 2 with hQlen | hQlen
        · -- `Q = [qk]`: red path `P ++ [qk]`, blue path `[a]`.
          have hQl : Q.toList = [qk] := by
            have h := eq_singleton_of_length_lt_two hQne hQlen
            rwa [← hqk] at h
          refine ⟨⟨P.toList ++ [qk], by simp, nodup_concat P.nodup hqkP⟩,
            ⟨[a], by simp, List.nodup_singleton a⟩, ?_, ?_, ?_, ?_⟩
          · exact isChain_concat hPne hP h3
          · exact List.isChain_singleton a
          · intro v
            show (v ∈ P.toList ++ [qk] ∨ v ∈ [a]) ↔ v ∈ insert a t
            rw [List.mem_append, List.mem_singleton, Finset.mem_insert, ← hcovL v]
            simp only [hQl, List.mem_singleton]
            tauto
          · intro v hv
            obtain ⟨hv1, hv2⟩ := hv
            have hv1' : v ∈ P.toList ++ [qk] := hv1
            have hv2' : v ∈ [a] := hv2
            rw [List.mem_singleton] at hv2'
            subst hv2'
            rw [List.mem_append, List.mem_singleton] at hv1'
            rcases hv1' with h | h
            · exact haP h
            · exact hqka h.symm
        · -- `|Q| ≥ 2`: red path `P ++ [qk, a]`, blue path `Q.dropLast`.
          refine ⟨⟨P.toList ++ [qk, a], by simp,
                nodup_concat_pair P.nodup hqkP haP hqka⟩,
              ⟨Q.toList.dropLast, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · intro hne
            rw [List.dropLast_eq_nil_iff] at hne
            omega
          · exact Q.nodup.sublist (List.dropLast_prefix _).sublist
          · exact isChain_concat_pair hPne hP h3 h2.symm
          · exact hQ.dropLast
          · intro v
            show (v ∈ P.toList ++ [qk, a] ∨ v ∈ Q.toList.dropLast) ↔ v ∈ insert a t
            rw [List.mem_append, List.mem_cons, List.mem_singleton, Finset.mem_insert,
              ← hcovL v, mem_iff_mem_dropLast hQne]
            tauto
          · intro v hv
            obtain ⟨hv1, hv2⟩ := hv
            have hv1' : v ∈ P.toList ++ [qk, a] := hv1
            have hv2' : v ∈ Q.toList.dropLast := hv2
            have hv2Q : v ∈ Q.toList := mem_of_mem_dropLast hv2'
            rw [List.mem_append, List.mem_cons, List.mem_singleton] at hv1'
            rcases hv1' with h | rfl | rfl
            · exact hd v ⟨h, hv2Q⟩
            · exact getLast_notMem_dropLast hQne Q.nodup hv2'
            · exact ha (hsubQ v hv2Q)
      · -- `pk–qk` is blue: move `pk` (and then `a`) onto the blue path.
        have hadjq : Color.adj G .blue pk qk := ⟨hpkqk, h3⟩
        rcases Nat.lt_or_ge P.toList.length 2 with hPlen | hPlen
        · -- `P = [pk]`: red path `[a]`, blue path `Q ++ [pk]`.
          have hPl : P.toList = [pk] := by
            have h := eq_singleton_of_length_lt_two hPne hPlen
            rwa [← hpk] at h
          refine ⟨⟨[a], by simp, List.nodup_singleton a⟩,
            ⟨Q.toList ++ [pk], by simp, nodup_concat Q.nodup hpkQ⟩, ?_, ?_, ?_, ?_⟩
          · exact List.isChain_singleton a
          · exact isChain_concat hQne hQ (Color.adj_symm G hadjq)
          · intro v
            show (v ∈ [a] ∨ v ∈ Q.toList ++ [pk]) ↔ v ∈ insert a t
            rw [List.mem_append, List.mem_singleton, Finset.mem_insert, ← hcovL v]
            simp only [hPl, List.mem_singleton]
            tauto
          · intro v hv
            obtain ⟨hv1, hv2⟩ := hv
            have hv1' : v ∈ [a] := hv1
            have hv2' : v ∈ Q.toList ++ [pk] := hv2
            rw [List.mem_singleton] at hv1'
            subst hv1'
            rw [List.mem_append, List.mem_singleton] at hv2'
            rcases hv2' with h | h
            · exact haQ h
            · exact hpka h.symm
        · -- `|P| ≥ 2`: red path `P.dropLast`, blue path `Q ++ [pk, a]`.
          refine ⟨⟨P.toList.dropLast, ?_, ?_⟩,
              ⟨Q.toList ++ [pk, a], by simp,
                nodup_concat_pair Q.nodup hpkQ haQ hpka⟩, ?_, ?_, ?_, ?_⟩
          · intro hne
            rw [List.dropLast_eq_nil_iff] at hne
            omega
          · exact P.nodup.sublist (List.dropLast_prefix _).sublist
          · exact hP.dropLast
          · exact isChain_concat_pair hQne hQ (Color.adj_symm G hadjq)
                (Color.adj_symm G hadjk)
          · intro v
            show (v ∈ P.toList.dropLast ∨ v ∈ Q.toList ++ [pk, a]) ↔ v ∈ insert a t
            rw [List.mem_append, List.mem_cons, List.mem_singleton, Finset.mem_insert,
              ← hcovL v, mem_iff_mem_dropLast hPne]
            tauto
          · intro v hv
            obtain ⟨hv1, hv2⟩ := hv
            have hv1' : v ∈ P.toList.dropLast := hv1
            have hv2' : v ∈ Q.toList ++ [pk, a] := hv2
            have hv1P : v ∈ P.toList := mem_of_mem_dropLast hv1'
            rw [List.mem_append, List.mem_cons, List.mem_singleton] at hv2'
            rcases hv2' with h | rfl | rfl
            · exact hd v ⟨hv1P, h⟩
            · exact getLast_notMem_dropLast hPne P.nodup hv1'
            · exact ha (hsubP v hv1P)
    · -- `a–qk` is blue: append `a` to the blue path.
      have hadj2 : Color.adj G .blue a qk := ⟨Ne.symm hqka, h2⟩
      refine ⟨P, ⟨Q.toList ++ [a], by simp, nodup_concat Q.nodup haQ⟩, hP, ?_, ?_, ?_⟩
      · exact isChain_concat hQne hQ (Color.adj_symm G hadj2)
      · intro v
        show (v ∈ P.toList ∨ v ∈ Q.toList ++ [a]) ↔ v ∈ insert a t
        rw [List.mem_append, List.mem_singleton, Finset.mem_insert, ← hcovL v]
        tauto
      · intro v hv
        obtain ⟨hv1, hv2⟩ := hv
        have hv1' : v ∈ P.toList := hv1
        have hv2' : v ∈ Q.toList ++ [a] := hv2
        rw [List.mem_append, List.mem_singleton] at hv2'
        rcases hv2' with h | rfl
        · exact hd v ⟨hv1', h⟩
        · exact haP hv1'

/-- **Disjoint red/blue partition**: any vertex set of cardinality at least
two can be partitioned into a red path and a blue path. -/
private theorem exists_two_path_partition (G : SimpleGraph W) {s : Finset W}
    (hs : s.Nontrivial) :
    ∃ P Q : VertPath W, P.IsMonochromatic G .red ∧ Q.IsMonochromatic G .blue ∧
      (∀ v, (v ∈ P ∨ v ∈ Q) ↔ v ∈ s) ∧ (∀ v, ¬ (v ∈ P ∧ v ∈ Q)) := by
  classical
  induction hs.nonempty using Finset.Nonempty.strong_induction with
  | h₀ b => exact absurd hs Finset.not_nontrivial_singleton
  | h₁ hnt ih =>
    rename_i u
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    have hne : (u.erase x).Nonempty :=
      ⟨y, Finset.mem_erase.mpr ⟨hxy.symm, hy⟩⟩
    by_cases ht2 : (u.erase x).Nontrivial
    · obtain ⟨P, Q, hP, hQ, hcov, hd⟩ :=
        ih _ hne (Finset.erase_ssubset hx) ht2
      obtain ⟨P', Q', hP', hQ', hcov', hd'⟩ :=
        extend_partition G (fun h => (Finset.mem_erase.mp h).1 rfl) hP hQ hcov hd
      rw [Finset.insert_erase hx] at hcov'
      exact ⟨P', Q', hP', hQ', hcov', hd'⟩
    · -- `u.erase x = {z}`, so `u = {x, z}`: two singleton paths.
      obtain ⟨z, hz⟩ := (hne.exists_eq_singleton_or_nontrivial).resolve_right ht2
      have hzx : z ≠ x := by
        have hz' : z ∈ u.erase x := hz ▸ Finset.mem_singleton_self z
        exact (Finset.mem_erase.mp hz').1
      have hs_eq : u = insert x {z} := hz ▸ (Finset.insert_erase hx).symm
      refine ⟨⟨[z], by simp, List.nodup_singleton z⟩,
        ⟨[x], by simp, List.nodup_singleton x⟩, ?_, ?_, ?_, ?_⟩
      · exact List.isChain_singleton z
      · exact List.isChain_singleton x
      · intro v
        show (v ∈ [z] ∨ v ∈ [x]) ↔ v ∈ u
        rw [hs_eq]
        simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_singleton]
        tauto
      · intro v hv
        obtain ⟨hv1, hv2⟩ := hv
        have hv1' : v ∈ [z] := hv1
        have hv2' : v ∈ [x] := hv2
        rw [List.mem_singleton] at hv1' hv2'
        exact hzx (hv1' ▸ hv2')

/-- **Gerencsér–Gyárfás** (PVW24 Theorem 1.1).  The vertex set of every
2-edge-coloured complete graph can be covered by two monochromatic paths;
the two paths may have different colours. -/
theorem gerencser_gyarfas {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) :
    ∃ (c₁ c₂ : Color) (p q : VertPath V),
      p.IsMonochromatic G c₁ ∧ q.IsMonochromatic G c₂ ∧
      ∀ v : V, v ∈ p ∨ v ∈ q := by
  classical
  have hu : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  rcases hu.exists_eq_singleton_or_nontrivial with ⟨v, hv⟩ | hnt
  · -- `V = {v}`: both paths are the singleton `[v]`.
    refine ⟨.red, .blue, ⟨[v], by simp, List.nodup_singleton v⟩,
      ⟨[v], by simp, List.nodup_singleton v⟩, ?_, ?_, ?_⟩
    · exact List.isChain_singleton v
    · exact List.isChain_singleton v
    · intro w
      left
      have h : w = v := Finset.mem_singleton.mp (hv ▸ Finset.mem_univ w)
      show w ∈ [v]
      rw [List.mem_singleton]
      exact h
  · obtain ⟨P, Q, hP, hQ, hcov, _⟩ := exists_two_path_partition G hnt
    exact ⟨.red, .blue, P, Q, hP, hQ, fun v => (hcov v).mpr (Finset.mem_univ v)⟩

/-- Corollary form used in the proof of Lemma 3.2: some monochromatic path
covers at least half the vertices. -/
theorem exists_mono_path_half {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) :
    ∃ c : Color, ∃ p : VertPath V, p.IsMonochromatic G c ∧
      Fintype.card V ≤ 2 * p.toList.length := by
  classical
  obtain ⟨c₁, c₂, p, q, hp, hq, hcov⟩ := gerencser_gyarfas G
  have hcard : Fintype.card V ≤ p.toList.length + q.toList.length := by
    have hsub : (Finset.univ : Finset V) ⊆ p.toList.toFinset ∪ q.toList.toFinset := by
      intro v _
      rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset]
      exact hcov v
    calc Fintype.card V = Finset.univ.card := (Finset.card_univ).symm
      _ ≤ (p.toList.toFinset ∪ q.toList.toFinset).card := Finset.card_le_card hsub
      _ ≤ p.toList.toFinset.card + q.toList.toFinset.card := Finset.card_union_le _ _
      _ = p.toList.length + q.toList.length := by
          rw [List.toFinset_card_of_nodup p.nodup, List.toFinset_card_of_nodup q.nodup]
  rcases Nat.lt_or_ge p.toList.length q.toList.length with h | h
  · exact ⟨c₂, q, hq, by omega⟩
  · exact ⟨c₁, p, hp, by omega⟩

end JSP415
