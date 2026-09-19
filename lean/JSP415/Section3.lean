import JSP415.Defs
import JSP415.Gerencser
import JSP415.BipLemmas

/-!
# Section 3 of PVW24: the inductive proof

Lemmas 3.1–3.3, Proposition 3.4, and the main Theorem 1.3.

Instead of the paper's `f(n,χ)` (least size of a same-colour monochromatic
path cover) we work directly with `HasCoverLe`/`HasCoverLt`/`AllCoverLt`:
`f(n,χ) ≤ b` iff `HasCoverLe G b`, and `f(m) < √m + C₁` for all `m < n` is
the strong-induction hypothesis `∀ m < n, AllCoverLt m (√m + C₁)`.
-/

open Finset

namespace JSP415

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PVW24 Lemma 3.1 (overlap lemma).**  If a large set `S` is covered by few
red paths and also by few blue paths, the induction hypothesis upgrades to a
strong bound at level `n`.

The hypothesis `S.Nonempty` is needed: the proof deletes `S` and applies the
induction hypothesis at `m = n - |S| < n`.  Without it the statement is false
already at `n = 0` (with `k = 0`, `S = ∅` and `C₁ < C₂ < 0` all hypotheses hold
while `HasCoverLe G C₂` fails, every cover having nonnegative cardinality). -/
theorem overlap_bound {n : ℕ} {C₁ C₂ : ℝ}
    (hind : ∀ m < n, AllCoverLt m (Real.sqrt m + C₁))
    (G : SimpleGraph (Fin n)) {k : ℕ}
    (PR : Fin k → VertPath (Fin n)) (hPR : ∀ i, (PR i).IsMonochromatic G .red)
    (QB : Fin k → VertPath (Fin n)) (hQB : ∀ i, (QB i).IsMonochromatic G .blue)
    (S : Finset (Fin n)) (hSne : S.Nonempty)
    (hS : ∀ s ∈ S, (∃ i, s ∈ PR i) ∧ (∃ i, s ∈ QB i))
    (hineq : Real.sqrt (n - S.card : ℝ) + C₁ + k ≤ Real.sqrt n + C₂) :
    HasCoverLe G (Real.sqrt n + C₂) := by
  classical
  -- Deleting `S` leaves `m = n - |S| < n` vertices.
  have hcardS : 0 < S.card := Finset.card_pos.mpr hSne
  have hSle : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hn : 0 < n := hcardS.trans_le hSle
  have hm : n - S.card < n := Nat.sub_lt hn hcardS
  have hcardW : Fintype.card ↥Sᶜ = n - S.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  -- Induction hypothesis on the induced colouring of `Sᶜ`.
  obtain ⟨c₀, P₀, ⟨hmono₀, hcov₀⟩, hlt₀⟩ :=
    hind (n - S.card) hm ↥Sᶜ hcardW (inducedColoring G Sᶜ)
  -- Normalise `hineq`: its `↑n - ↑#S` is `↑(n - #S)` since `#S ≤ n`.
  have hcast : ((n - S.card : ℕ) : ℝ) = (n : ℝ) - S.card := Nat.cast_sub hSle
  rw [← hcast] at hineq
  have hinj : Function.Injective (Subtype.val : ↥Sᶜ → Fin n) := Subtype.val_injective
  have hmapinj : Function.Injective fun p : VertPath ↥Sᶜ ↦ p.map Subtype.val hinj :=
    fun p q hpq ↦
      VertPath.ext (List.map_injective_iff.mpr hinj (congrArg VertPath.toList hpq))
  -- Push the `Sᶜ`-cover forward and adjoin the `k` given paths of colour `c₀`.
  cases c₀ with
  | red =>
    refine ⟨.red, P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪ univ.image PR,
      ⟨⟨?_, ?_⟩, ?_⟩⟩
    · intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
        exact (hmono₀ p hp).map hinj
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
        exact hPR i
    · intro v
      by_cases hvS : v ∈ S
      · obtain ⟨⟨i, hi⟩, -⟩ := hS v hvS
        exact ⟨PR i, Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), hi⟩
      · obtain ⟨p, hp, hvp⟩ := hcov₀ ⟨v, Finset.mem_compl.mpr hvS⟩
        exact ⟨p.map Subtype.val hinj, Finset.mem_union_left _
          (Finset.mem_map.mpr ⟨p, hp, rfl⟩),
          VertPath.mem_map.mpr ⟨⟨v, Finset.mem_compl.mpr hvS⟩, hvp, rfl⟩⟩
    · have him : (univ.image PR).card ≤ k := by
        calc (univ.image PR).card ≤ univ.card := Finset.card_image_le
        _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      have hcard : ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪
            univ.image PR).card : ℝ) ≤ P₀.card + k := by
        calc ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪
                univ.image PR).card : ℝ)
            ≤ ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩).card : ℝ) +
              ((univ.image PR).card : ℝ) := by
                exact_mod_cast Finset.card_union_le _ _
          _ ≤ P₀.card + k := by
              rw [Finset.card_map]
              have him' : ((univ.image PR).card : ℝ) ≤ k := by exact_mod_cast him
              linarith
      exact le_of_lt (lt_of_lt_of_le
        (lt_of_le_of_lt hcard (by linarith [hlt₀])) hineq)
  | blue =>
    refine ⟨.blue, P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪ univ.image QB,
      ⟨⟨?_, ?_⟩, ?_⟩⟩
    · intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
        exact (hmono₀ p hp).map hinj
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
        exact hQB i
    · intro v
      by_cases hvS : v ∈ S
      · obtain ⟨-, ⟨i, hi⟩⟩ := hS v hvS
        exact ⟨QB i, Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), hi⟩
      · obtain ⟨p, hp, hvp⟩ := hcov₀ ⟨v, Finset.mem_compl.mpr hvS⟩
        exact ⟨p.map Subtype.val hinj, Finset.mem_union_left _
          (Finset.mem_map.mpr ⟨p, hp, rfl⟩),
          VertPath.mem_map.mpr ⟨⟨v, Finset.mem_compl.mpr hvS⟩, hvp, rfl⟩⟩
    · have him : (univ.image QB).card ≤ k := by
        calc (univ.image QB).card ≤ univ.card := Finset.card_image_le
        _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      have hcard : ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪
            univ.image QB).card : ℝ) ≤ P₀.card + k := by
        calc ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪
                univ.image QB).card : ℝ)
            ≤ ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩).card : ℝ) +
              ((univ.image QB).card : ℝ) := by
                exact_mod_cast Finset.card_union_le _ _
          _ ≤ P₀.card + k := by
              rw [Finset.card_map]
              have him' : ((univ.image QB).card : ℝ) ≤ k := by exact_mod_cast him
              linarith
      exact le_of_lt (lt_of_lt_of_le
        (lt_of_le_of_lt hcard (by linarith [hlt₀])) hineq)

/-- **PVW24 Lemma 3.1, second part.**  The two-path special case: a set of
size `≥ 2Δ√n` covered by one red and one blue path already gives the bound,
where `Δ = C₁ − C₂ + 1`. -/
theorem overlap_bound_pair {n : ℕ} {C₁ C₂ : ℝ} (hC : C₂ ≤ C₁)
    (hind : ∀ m < n, AllCoverLt m (Real.sqrt m + C₁))
    (G : SimpleGraph (Fin n))
    (P : VertPath (Fin n)) (hP : P.IsMonochromatic G .red)
    (Q : VertPath (Fin n)) (hQ : Q.IsMonochromatic G .blue)
    (S : Finset (Fin n))
    (hS : ∀ s ∈ S, s ∈ P ∧ s ∈ Q)
    (hcard : 2 * (C₁ - C₂ + 1) * Real.sqrt n ≤ (S.card : ℝ)) :
    HasCoverLe G (Real.sqrt n + C₂) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0` is impossible: `P` is a nonempty list of `Fin 0` vertices.
    rcases P with ⟨l, hne, -⟩
    cases l with
    | nil => exact absurd rfl hne
    | cons v _ => exact absurd v.isLt (Nat.not_lt_zero _)
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn'
    have hΔ : 0 ≤ C₁ - C₂ + 1 := by linarith
    have hΔpos : (0 : ℝ) < C₁ - C₂ + 1 := by linarith
    have hSle : S.card ≤ n := by simpa using Finset.card_le_univ S
    -- `|S| ≥ 2Δ√n > 0`, so `S` is nonempty.
    have hSpos : (0 : ℝ) < (S.card : ℝ) :=
      lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) hΔpos) hsn) hcard
    have hSne : S.Nonempty :=
      Finset.card_pos.mp (by exact_mod_cast hSpos)
    -- Since `2Δ√n ≤ |S| ≤ n` we get `Δ ≤ √n`.
    have hΔle : C₁ - C₂ + 1 ≤ Real.sqrt n := by
      have h1 : 2 * (C₁ - C₂ + 1) * Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by
        refine hcard.trans ?_
        rw [Real.mul_self_sqrt hn'.le]
        exact_mod_cast hSle
      have h2 : 2 * (C₁ - C₂ + 1) ≤ Real.sqrt n :=
        le_of_mul_le_mul_right h1 hsn
      linarith
    -- `(√n - Δ)² = n - 2Δ√n + Δ² ≥ n - |S|`, hence `√(n - |S|) ≤ √n - Δ`.
    have hsqrt : Real.sqrt ((n - S.card : ℕ) : ℝ) ≤
        Real.sqrt n - (C₁ - C₂ + 1) := by
      rw [Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ Real.sqrt n - (C₁ - C₂ + 1))]
      rw [Nat.cast_sub hSle]
      have hsq : (Real.sqrt n - (C₁ - C₂ + 1)) ^ 2 =
          (n : ℝ) - 2 * (C₁ - C₂ + 1) * Real.sqrt n + (C₁ - C₂ + 1) ^ 2 := by
        have h2 := Real.sq_sqrt hn'.le
        ring_nf
        linarith
      rw [hsq]
      linarith [hcard, sq_nonneg (C₁ - C₂ + 1)]
    -- Apply `overlap_bound` with `k = 1`, the families `{P}` and `{Q}`.
    exact overlap_bound hind G (fun _ : Fin 1 ↦ P) (fun _ ↦ hP)
      (fun _ : Fin 1 ↦ Q) (fun _ ↦ hQ) S hSne
      (fun s hs ↦ ⟨⟨0, (hS s hs).1⟩, ⟨0, (hS s hs).2⟩⟩)
      (by rw [← Nat.cast_sub hSle, Nat.cast_one]; linarith [hsqrt])

section LongPathStructure

/-- The opposite colour. -/
private def Color.other : Color → Color
  | .red => .blue
  | .blue => .red

private theorem Color.other_ne (c : Color) : c.other ≠ c := by
  cases c <;> decide

private theorem Color.other_other (c : Color) : c.other.other = c := by
  cases c <;> rfl

/-- For distinct vertices, `c`-adjacency is exactly the failure of
`c.other`-adjacency. -/
private theorem Color.adj_iff_not_adj_other {V : Type*} (G : SimpleGraph V)
    {c : Color} {a b : V} (h : a ≠ b) :
    Color.adj G c a b ↔ ¬ Color.adj G c.other a b := by
  cases c
  · refine ⟨fun h1 h2 ↦ h2.2 h1, fun h1 ↦ ?_⟩
    by_contra h2
    exact h1 ⟨h, h2⟩
  · exact ⟨fun h1 h2 ↦ h1.2 h2, fun h1 ↦ ⟨h, h1⟩⟩

/-- For distinct vertices, one of the two colour adjacencies holds. -/
private theorem Color.adj_or_adj_other {V : Type*} (G : SimpleGraph V)
    {c : Color} {a b : V} (h : a ≠ b) :
    Color.adj G c a b ∨ Color.adj G c.other a b := by
  by_cases h1 : Color.adj G c a b
  · exact Or.inl h1
  · right
    apply (Color.adj_iff_not_adj_other G (c := c.other) h).mpr
    rw [Color.other_other]
    exact h1

/-- `adjXY` edges are colour-`c` edges (vertices on opposite sides differ). -/
private theorem adjXY_to_adj {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {X Y : Finset V} (hXY : Disjoint X Y) {c : Color} {a b : V}
    (h : Color.adjXY G X Y c a b) : Color.adj G c a b := by
  cases c
  · exact h.2
  · refine ⟨?_, h.2⟩
    intro hab
    subst hab
    rcases h.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (Finset.disjoint_left.mp hXY h1) h2
    · exact (Finset.disjoint_left.mp hXY h2) h1

/-- A longest `R`-chain among vertex paths exists, by `Nat.findGreatest`. -/
private theorem exists_longest_chain {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (v₀ : V) :
    ∃ p : VertPath V, p.toList.IsChain R ∧
      ∀ q : VertPath V, q.toList.IsChain R → q.toList.length ≤ p.toList.length := by
  classical
  haveI : Nonempty V := ⟨v₀⟩
  have hPM := Nat.findGreatest_spec
    (P := fun m ↦ ∃ p : VertPath V, p.toList.IsChain R ∧ p.toList.length = m)
    (n := Fintype.card V) Fintype.card_pos (m := 1)
    ⟨VertPath.singleton v₀, List.isChain_singleton v₀, rfl⟩
  obtain ⟨p, hp, hlen⟩ := hPM
  refine ⟨p, hp, fun q hq ↦ ?_⟩
  have hle : q.toList.length ≤ Fintype.card V := q.nodup.length_le_card
  have h2 : q.toList.length ≤ Nat.findGreatest
      (fun m ↦ ∃ p : VertPath V, p.toList.IsChain R ∧ p.toList.length = m)
      (Fintype.card V) := Nat.le_findGreatest hle ⟨q, hq, rfl⟩
  omega

/-- Prepending a `c`-adjacent fresh vertex gives a longer `c`-chain. -/
private theorem extend_head {n : ℕ} {G : SimpleGraph (Fin n)} {c : Color}
    {l : List (Fin n)} (hne : l ≠ []) (hchain : l.IsChain (Color.adj G c))
    (hnd : l.Nodup) {y : Fin n} (hy : y ∉ l)
    (h : Color.adj G c (l.head hne) y) :
    ∃ p : VertPath (Fin n), p.IsMonochromatic G c ∧
      p.toList.length = l.length + 1 := by
  refine ⟨⟨y :: l, by simp, List.nodup_cons.mpr ⟨hy, hnd⟩⟩, ?_, ?_⟩
  · refine hchain.cons fun z hz ↦ ?_
    rw [List.head?_eq_some_head hne, Option.mem_some] at hz
    rw [← hz]
    exact Color.adj_symm G h
  · rw [List.length_cons]

/-- `getD` with a valid index equals `getElem`. -/
private theorem list_getD_eq_getElem {α : Type*} {l : List α} {i : ℕ} {d : α}
    (h : i < l.length) : l.getD i d = l[i]'h := by
  rw [List.getD_eq_getElem?_getD, _root_.getElem?_pos l i h]
  rfl

/-- The detour `v₁…vᵢ vⱼ vⱼ₋₁…vᵢ₊₁ y vⱼ₊₁…vᵣ`: a longer `c`-chain through a
fresh vertex `y`, using the edges `vᵢvⱼ`, `vᵢ₊₁y`, `yvⱼ₊₁`. -/
private theorem detour_path {n : ℕ} {G : SimpleGraph (Fin n)} {c : Color}
    {l : List (Fin n)} (hchain : l.IsChain (Color.adj G c)) (hnd : l.Nodup)
    {y : Fin n} (hy : y ∉ l)
    {i j : ℕ} (hij : i < j) (hj : j + 1 < l.length)
    (hedge : Color.adj G c l[i] l[j])
    (h1 : Color.adj G c l[i+1] y) (h2 : Color.adj G c l[j+1] y) :
    ∃ p : VertPath (Fin n), p.IsMonochromatic G c ∧
      p.toList.length = l.length + 1 := by
  have hi : i + 1 < l.length := by omega
  set pre := l.take (i + 1) with hpre_def
  set mid := (l.drop (i + 1)).take (j - i) with hmid_def
  set suf := l.drop (j + 1) with hsuf_def
  -- `l` decomposes as `(pre ++ mid) ++ suf`.
  have hsplit : pre ++ mid ++ suf = l := by
    have e1 : l.take (i + 1) ++ (l.drop (i + 1)).take (j - i) = l.take (j + 1) := by
      have h : l.take (i + 1 + (j - i)) = l.take (i + 1) ++ (l.drop (i + 1)).take (j - i) :=
        List.take_add
      rw [show i + 1 + (j - i) = j + 1 by omega] at h
      exact h.symm
    rw [hpre_def, hmid_def, hsuf_def, e1, List.take_append_drop]
  -- nodup of the three blocks.
  have hnd' : (pre ++ mid ++ suf).Nodup := by rw [hsplit]; exact hnd
  obtain ⟨hpm_nd, hsuf_nd, hdisj_suf⟩ := List.nodup_append.mp hnd'
  obtain ⟨hpre_nd, hmid_nd, hdisj_mid⟩ := List.nodup_append.mp hpm_nd
  have hmidr_nd : mid.reverse.Nodup := List.nodup_reverse.mpr hmid_nd
  have hmem : ∀ x ∈ pre ++ mid ++ suf, x ∈ l := fun x hx ↦ by
    rw [hsplit] at hx; exact hx
  have hmem_pm : ∀ x ∈ pre ++ mid, x ∈ pre ++ mid ++ suf := fun x hx ↦
    List.mem_append_left suf hx
  have hD_nd : (pre ++ mid.reverse ++ [y] ++ suf).Nodup := by
    rw [List.nodup_append]
    refine ⟨?_, hsuf_nd, ?_⟩
    · rw [List.nodup_append]
      refine ⟨?_, List.nodup_singleton y, ?_⟩
      · rw [List.nodup_append]
        exact ⟨hpre_nd, hmidr_nd,
          fun a ha b hb ↦ hdisj_mid a ha b (List.mem_reverse.mp hb)⟩
      · intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        intro e
        apply hy
        have ham : a ∈ pre ++ mid := by
          rw [List.mem_append] at ha
          rcases ha with ha | ha
          · exact List.mem_append_left _ ha
          · exact List.mem_append_right _ (List.mem_reverse.mp ha)
        exact e ▸ hmem a (hmem_pm a ham)
    · intro a ha b hb
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · rw [List.mem_append] at ha
        rcases ha with ha | ha
        · exact hdisj_suf a (List.mem_append_left _ ha) b hb
        · exact hdisj_suf a (List.mem_append_right _ (List.mem_reverse.mp ha)) b hb
      · rw [List.mem_singleton] at ha
        subst ha
        intro e
        apply hy
        exact e.symm ▸ hmem b (List.mem_append_right _ hb)
  -- boundary values
  have hpre_last : pre.getLast? = some l[i] := by
    have hlen : (l.take (i + 1)).length = i + 1 := by
      rw [List.length_take]; omega
    rw [hpre_def, List.getLast?_eq_getElem?, hlen]
    show (l.take (i + 1))[i]? = _
    rw [List.getElem?_take, ite_eq_left (show i < i + 1 by omega)]
    exact List.getElem?_eq_getElem (show i < l.length by omega)
  have hmidr_head : mid.reverse.head? = some l[j] := by
    rw [List.head?_reverse, hmid_def, List.getLast?_eq_getElem?]
    have hlen : ((l.drop (i + 1)).take (j - i)).length = j - i := by
      rw [List.length_take, List.length_drop]; omega
    rw [hlen]
    show ((l.drop (i + 1)).take (j - i))[j - i - 1]? = _
    rw [List.getElem?_take, ite_eq_left (show j - i - 1 < j - i by omega),
      List.getElem?_drop]
    have e : i + 1 + (j - i - 1) = j := by omega
    rw [e]
    exact List.getElem?_eq_getElem (show j < l.length by omega)
  have hmidr_last : mid.reverse.getLast? = some l[i+1] := by
    rw [List.getLast?_reverse, List.head?_eq_getElem?, hmid_def,
      List.getElem?_take, ite_eq_left (show 0 < j - i by omega), List.getElem?_drop]
    exact List.getElem?_eq_getElem hi
  have hsuf_head : suf.head? = some l[j+1] := by
    rw [hsuf_def, List.head?_drop]
    exact List.getElem?_eq_getElem hj
  -- the chain: `((pre ++ mid.reverse) ++ [y]) ++ suf`
  have hD_ch : (pre ++ mid.reverse ++ [y] ++ suf).IsChain (Color.adj G c) := by
    have hpre_ch := hchain.take (i + 1)
    have hmid_ch := (hchain.drop (i + 1)).take (j - i)
    have hrev_ch : mid.reverse.IsChain (Color.adj G c) :=
      List.isChain_reverse.mpr (hmid_ch.imp fun _ _ h ↦ Color.adj_symm G h)
    have hsuf_ch := hchain.drop (j + 1)
    refine ((hpre_ch.append hrev_ch ?_).append
        (List.isChain_singleton y) ?_).append hsuf_ch ?_
    · intro a ha b hb
      rw [hpre_last, Option.mem_some] at ha
      rw [hmidr_head, Option.mem_some] at hb
      rw [← ha, ← hb]
      exact hedge
    · intro a ha b hb
      rw [List.getLast?_append, hmidr_last] at ha
      have e : (Option.some l[i+1]).or pre.getLast? = some l[i+1] := rfl
      rw [e, Option.mem_some] at ha
      rw [List.head?_singleton, Option.mem_some] at hb
      rw [← ha, ← hb]
      exact h1
    · intro a ha b hb
      rw [List.getLast?_append, List.getLast?_singleton] at ha
      have e : (Option.some y).or (pre ++ mid.reverse).getLast? = some y := rfl
      rw [e, Option.mem_some] at ha
      rw [hsuf_head, Option.mem_some] at hb
      rw [← ha, ← hb]
      exact Color.adj_symm G h2
  have hD_len : (pre ++ mid.reverse ++ [y] ++ suf).length = l.length + 1 := by
    have hp : pre.length = i + 1 := by rw [hpre_def, List.length_take]; omega
    have hm : mid.reverse.length = j - i := by
      rw [List.length_reverse, hmid_def, List.length_take, List.length_drop]; omega
    have hs : suf.length = l.length - (j + 1) := by
      rw [hsuf_def, List.length_drop]
    rw [List.length_append, List.length_append, List.length_append,
      List.length_singleton, hp, hm, hs]
    omega
  exact ⟨⟨_, by simp, hD_nd⟩, hD_ch, hD_len⟩

/-- In an `adjXY`-chain, consecutive vertices alternate sides; hence at least
`(l.length - 1)/2` vertices lie on the `X` side. -/
private theorem alternation_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {X Y : Finset V} (hXY : Disjoint X Y) {c : Color}
    {l : List V} (hchain : l.IsChain (Color.adjXY G X Y c)) (hnd : l.Nodup) :
    l.length ≤ 2 * (l.toFinset ∩ X).card + 1 := by
  revert hchain hnd
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton a =>
    intro _ _
    show 1 ≤ 2 * ([a].toFinset ∩ X).card + 1
    omega
  | cons_cons a b t ih =>
    intro hchain hnd
    rw [List.isChain_cons_cons] at hchain
    obtain ⟨hab, htail⟩ := hchain
    rw [List.nodup_cons] at hnd
    obtain ⟨ha_notin, hbnd⟩ := hnd
    have ha_notin' : a ∉ t := fun h ↦ ha_notin (List.mem_cons_of_mem b h)
    have ht_nd : t.Nodup := hbnd.tail
    have hb_notin : b ∉ t := (List.nodup_cons.mp hbnd).1
    have hofX : (a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X) := by
      rcases bip_ramsey_path.Color.adjXY.across hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, (Finset.disjoint_left.mp hXY.symm h2)⟩
      · exact Or.inr ⟨h2, (Finset.disjoint_left.mp hXY.symm h1)⟩
    have hcard : ((a :: b :: t).toFinset ∩ X).card = (t.toFinset ∩ X).card + 1 := by
      rcases hofX with ⟨haX, hbX⟩ | ⟨hbX, haX⟩
      · have e : (a :: b :: t).toFinset ∩ X = insert a (t.toFinset ∩ X) := by
          rw [List.toFinset_cons, List.toFinset_cons,
            Finset.insert_inter_of_mem haX, Finset.insert_inter_of_notMem hbX]
        rw [e, Finset.card_insert_of_notMem (by
          simp only [Finset.mem_inter, List.mem_toFinset]
          exact fun h ↦ ha_notin' h.1)]
      · have e : (a :: b :: t).toFinset ∩ X = insert b (t.toFinset ∩ X) := by
          rw [List.toFinset_cons, List.toFinset_cons,
            Finset.insert_inter_of_notMem haX, Finset.insert_inter_of_mem hbX]
        rw [e, Finset.card_insert_of_notMem (by
          simp only [Finset.mem_inter, List.mem_toFinset]
          exact fun h ↦ hb_notin h.1)]
    have hih := ih htail.tail ht_nd
    rw [List.length_cons, List.length_cons, hcard]
    omega

/-- A set `S` covered both by a `γ`-path and by a `γ.other`-path of size
`≥ 2Δ√n` gives a cover, contradicting `hG`. -/
private theorem overlap_pair_absurd {n : ℕ} {C₁ C₂ : ℝ} (hC : C₂ ≤ C₁)
    (hind : ∀ m < n, AllCoverLt m (Real.sqrt m + C₁))
    {G : SimpleGraph (Fin n)} (hG : ¬ HasCoverLe G (Real.sqrt n + C₂))
    {γ : Color} (P Q : VertPath (Fin n))
    (hP : P.IsMonochromatic G γ) (hQ : Q.IsMonochromatic G γ.other)
    (S : Finset (Fin n)) (hS : ∀ s ∈ S, s ∈ P ∧ s ∈ Q)
    (hcard : 2 * (C₁ - C₂ + 1) * Real.sqrt n ≤ (S.card : ℝ)) : False := by
  cases γ with
  | red =>
    have hQ' : Q.IsMonochromatic G .blue := hQ
    exact hG (overlap_bound_pair hC hind G P hP Q hQ' S hS hcard)
  | blue =>
    have hP' : P.IsMonochromatic G .blue := hP
    have hQ' : Q.IsMonochromatic G .red := hQ
    exact hG (overlap_bound_pair hC hind G Q hQ' P hP' S
      (fun s hs ↦ ⟨(hS s hs).2, (hS s hs).1⟩) hcard)

/-- **Few `γ`-neighbours on a longest `γ`-path.**  A vertex `y` off a longest
`γ`-chain `l` has at most `2Δ√n` `γ`-neighbours on `l`: the predecessors of
those neighbours form a `γ.other`-clique, hence a `γ.other`-path on `l`,
which is excluded by `overlap_pair_absurd`. -/
private theorem few_nbrs_on_path {n : ℕ} {C₁ C₂ : ℝ} (hC : C₂ ≤ C₁)
    (hind : ∀ m < n, AllCoverLt m (Real.sqrt m + C₁))
    {G : SimpleGraph (Fin n)} (hG : ¬ HasCoverLe G (Real.sqrt n + C₂))
    (hn0 : 0 < n) {γ : Color} {l : List (Fin n)}
    (hchain : l.IsChain (Color.adj G γ)) (hnd : l.Nodup)
    (hmax : ∀ q : VertPath (Fin n), q.toList.IsChain (Color.adj G γ) →
      q.toList.length ≤ l.length)
    {y : Fin n} (hy : y ∉ l) :
    (Set.ncard {x : Fin n | x ∈ l ∧ Color.adj G γ x y} : ℝ) ≤
      2 * (C₁ - C₂ + 1) * Real.sqrt n := by
  classical
  set B := l.toFinset.filter (fun x ↦ Color.adj G γ x y) with hB_def
  have hBset : {x : Fin n | x ∈ l ∧ Color.adj G γ x y} = (B : Set (Fin n)) := by
    ext x
    simp [hB_def, Finset.coe_filter]
  have hΔpos : (0:ℝ) < C₁ - C₂ + 1 := by linarith
  have hsqrtpos : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
  by_cases hne : l = []
  · subst hne
    have hB : B = ∅ := by simp [hB_def]
    rw [hBset, hB, Finset.coe_empty, Set.ncard_empty, Nat.cast_zero]
    positivity
  have hlen0 : 0 < l.length := by
    cases l with
    | nil => exact absurd rfl hne
    | cons x t => simp
  -- No `γ`-edge from the head of `l` to `y` (else `y :: l` is longer).
  have hhead : ¬ Color.adj G γ (l[0]'hlen0) y := by
    intro h
    have h' : Color.adj G γ (l.head hne) y := by
      rwa [List.head_eq_getElem_zero]
    obtain ⟨q, hqmono, hqlen⟩ := extend_head hne hchain hnd hy h'
    have := hmax q hqmono
    omega
  -- the predecessor finset `T` and its members' properties
  set T := l.dropLast.toFinset.filter
    (fun x ↦ l.getD (l.idxOf x + 1) x ∈ B) with hT_def
  have hTmem : ∀ x ∈ T, x ∈ l.dropLast ∧ l.getD (l.idxOf x + 1) x ∈ B := by
    intro x hx
    rw [hT_def, Finset.mem_filter, List.mem_toFinset] at hx
    exact hx
  have hTl : ∀ x ∈ T, x ∈ l := by
    intro x hx
    exact List.Sublist.mem (hTmem x hx).1 (List.dropLast_prefix l).sublist
  have hBmem : ∀ b ∈ B, b ∈ l ∧ Color.adj G γ b y := by
    intro b hb
    rw [hB_def, Finset.mem_filter, List.mem_toFinset] at hb
    exact hb
  have hTsuc : ∀ x ∈ T, l.idxOf x + 1 < l.length ∧
      Color.adj G γ (l.getD (l.idxOf x + 1) x) y := by
    intro x hx
    obtain ⟨hxd, hxs⟩ := hTmem x hx
    exact ⟨List.succ_idxOf_lt_length_of_mem_dropLast hxd, (hBmem _ hxs).2⟩
  have hidxpos : ∀ b ∈ B, 1 ≤ l.idxOf b := by
    intro b hb
    obtain ⟨hbl, hadj⟩ := hBmem b hb
    have hidx : l.idxOf b < l.length := List.idxOf_lt_length_of_mem hbl
    by_contra h0
    have h0' : l.idxOf b = 0 := by omega
    have e : l[0]'hlen0 = b := by
      calc l[0]'hlen0 = l.get ⟨l.idxOf b, hidx⟩ :=
            congrArg l.get (Fin.ext h0').symm
        _ = l[l.idxOf b]'hidx := rfl
        _ = b := List.getElem_idxOf hidx
    exact hhead (e ▸ hadj)
  -- `l.idxOf` of a `getElem` is the index itself.
  have hidx_get : ∀ {p : ℕ} (hp : p < l.length), l.idxOf (l[p]'hp) = p := by
    intro p hp
    exact hnd.idxOf_getElem p hp
  -- the predecessor map sends `B` into `T` injectively.
  have hg_maps : ∀ b ∈ B, l.getD (l.idxOf b - 1) b ∈ T := by
    intro b hb
    obtain ⟨hbl, hadj⟩ := hBmem b hb
    have hidx : l.idxOf b < l.length := List.idxOf_lt_length_of_mem hbl
    have hidx1 := hidxpos b hb
    have hp : l.idxOf b - 1 < l.length := by omega
    have hgb : l.getD (l.idxOf b - 1) b = l[l.idxOf b - 1]'hp :=
      list_getD_eq_getElem hp
    rw [hT_def, Finset.mem_filter, hgb]
    refine ⟨?_, ?_⟩
    · rw [List.mem_toFinset,
        List.mem_dropLast_iff_idxOf_lt (List.getElem_mem _), hidx_get hp]
      omega
    · have esucc : l.getD (l.idxOf (l[l.idxOf b - 1]'hp) + 1) (l[l.idxOf b - 1]'hp) = b := by
        rw [hidx_get hp]
        have e : l.idxOf b - 1 + 1 = l.idxOf b := by omega
        rw [e, list_getD_eq_getElem hidx, List.getElem_idxOf hidx]
      rw [esucc]
      exact hb
  have hg_inj : Set.InjOn (fun b ↦ l.getD (l.idxOf b - 1) b) B := by
    intro b1 hb1 b2 hb2 heq
    obtain ⟨hb1l, -⟩ := hBmem b1 hb1
    obtain ⟨hb2l, -⟩ := hBmem b2 hb2
    have hi1 : l.idxOf b1 < l.length := List.idxOf_lt_length_of_mem hb1l
    have hi2 : l.idxOf b2 < l.length := List.idxOf_lt_length_of_mem hb2l
    have hp1 := hidxpos b1 hb1
    have hp2 := hidxpos b2 hb2
    have hpr1 : l.idxOf b1 - 1 < l.length := by omega
    have hpr2 : l.idxOf b2 - 1 < l.length := by omega
    have hg1 : l.getD (l.idxOf b1 - 1) b1 = l[l.idxOf b1 - 1]'hpr1 :=
      list_getD_eq_getElem hpr1
    have hg2 : l.getD (l.idxOf b2 - 1) b2 = l[l.idxOf b2 - 1]'hpr2 :=
      list_getD_eq_getElem hpr2
    dsimp only at heq
    rw [hg1, hg2] at heq
    have hpi : l.idxOf b1 - 1 = l.idxOf b2 - 1 := (hnd.getElem_inj_iff).mp heq
    have hii : l.idxOf b1 = l.idxOf b2 := by omega
    calc b1 = l[l.idxOf b1]'hi1 := (List.getElem_idxOf hi1).symm
      _ = l[l.idxOf b2]'hi2 := congrArg (fun i : Fin l.length ↦ l.get i) (Fin.ext hii)
      _ = b2 := List.getElem_idxOf hi2
  have hBT : B.card ≤ T.card :=
    Finset.card_le_card_of_injOn _ (fun b hb ↦ hg_maps b hb) hg_inj
  -- predecessors form a `γ.other`-clique
  have hclique : ∀ a b, a ∈ T → b ∈ T → a ≠ b → Color.adj G γ.other a b := by
    have core : ∀ a b, a ∈ T → b ∈ T → l.idxOf a < l.idxOf b →
        Color.adj G γ.other a b := by
      intro a b haT hbT hlt
      obtain ⟨ha_len, ha_adj⟩ := hTsuc a haT
      obtain ⟨hb_len, hb_adj⟩ := hTsuc b hbT
      have hia : l.idxOf a < l.length := List.idxOf_lt_length_of_mem (hTl a haT)
      have hib : l.idxOf b < l.length := List.idxOf_lt_length_of_mem (hTl b hbT)
      have hpa : l[l.idxOf a]'hia = a := List.getElem_idxOf hia
      have hpb : l[l.idxOf b]'hib = b := List.getElem_idxOf hib
      have hne : a ≠ b := fun e ↦ absurd e (fun h ↦ by rw [h] at hlt; omega)
      by_contra hnot
      have hab : Color.adj G γ a b := (Color.adj_iff_not_adj_other G hne).mpr hnot
      have e1 : l.getD (l.idxOf a + 1) a = l[l.idxOf a + 1]'ha_len :=
        list_getD_eq_getElem ha_len
      have e2 : l.getD (l.idxOf b + 1) b = l[l.idxOf b + 1]'hb_len :=
        list_getD_eq_getElem hb_len
      have hedge' : Color.adj G γ (l[l.idxOf a]'hia) (l[l.idxOf b]'hib) := by
        rw [hpa, hpb]; exact hab
      obtain ⟨q, hqmono, hqlen⟩ := detour_path hchain hnd hy hlt hb_len
        hedge' (e1 ▸ ha_adj) (e2 ▸ hb_adj)
      have := hmax q hqmono
      omega
    intro a b haT hbT hne
    have hia : l.idxOf a < l.length := List.idxOf_lt_length_of_mem (hTl a haT)
    have hib : l.idxOf b < l.length := List.idxOf_lt_length_of_mem (hTl b hbT)
    have hpa : l[l.idxOf a]'hia = a := List.getElem_idxOf hia
    have hpb : l[l.idxOf b]'hib = b := List.getElem_idxOf hib
    have hpos : l.idxOf a ≠ l.idxOf b := by
      intro e
      apply hne
      calc a = l[l.idxOf a]'hia := hpa.symm
        _ = l[l.idxOf b]'hib := congrArg (fun i : Fin l.length ↦ l.get i) (Fin.ext e)
        _ = b := hpb
    rcases lt_or_gt_of_ne hpos with hlt | hgt
    · exact core a b haT hbT hlt
    · exact Color.adj_symm G (core b a hbT haT hgt)
  -- the `γ.other`-chain on `T` (in `l`-order)
  set pred := l.filter (fun x ↦ decide (x ∈ T)) with hpred_def
  have hpred_nd : pred.Nodup := hnd.sublist List.filter_sublist
  have hpred_mem : ∀ x ∈ pred, x ∈ T := by
    intro x hx
    rw [hpred_def, List.mem_filter] at hx
    exact of_decide_eq_true hx.2
  have hpred_chain : pred.IsChain (Color.adj G γ.other) := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro a b l₁ l₂ heq
    have ha : a ∈ pred := by
      rw [heq]
      exact List.mem_append_right l₁ List.mem_cons_self
    have hb : b ∈ pred := by
      rw [heq]
      exact List.mem_append_right l₁
        (List.mem_cons_of_mem a List.mem_cons_self)
    have hne : a ≠ b := by
      have hnd2 : (l₁ ++ a :: b :: l₂).Nodup := heq ▸ hpred_nd
      obtain ⟨-, h3, -⟩ := List.nodup_append.mp hnd2
      obtain ⟨ha', -⟩ := List.nodup_cons.mp h3
      intro e
      subst e
      exact ha' List.mem_cons_self
    exact hclique a b (hpred_mem a ha) (hpred_mem b hb) hne
  have hpred_tf : pred.toFinset = T := by
    ext x
    rw [List.mem_toFinset, hpred_def, List.mem_filter]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hxl, hxT⟩
      exact hxT
    · intro hxT
      exact ⟨hTl x hxT, hxT⟩
  have hpred_len : pred.length = T.card := by
    rw [← List.toFinset_card_of_nodup hpred_nd, hpred_tf]
  -- `|T| ≥ 2Δ√n` would contradict `hG`.
  have hTlt : (T.card : ℝ) < 2 * (C₁ - C₂ + 1) * Real.sqrt n := by
    by_contra hge
    push Not at hge
    have hpos : (0:ℝ) < T.card :=
      lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) hΔpos) hsqrtpos) hge
    have hTne : T.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpos)
    obtain ⟨x, hxT⟩ := hTne
    have hpred_ne : pred ≠ [] := by
      have hx : x ∈ pred := by
        rw [hpred_def, List.mem_filter]
        exact ⟨hTl x hxT, by rw [decide_eq_true_eq]; exact hxT⟩
      intro e
      rw [e] at hx
      simp at hx
    exact overlap_pair_absurd hC hind hG
      ⟨l, hne, hnd⟩ ⟨pred, hpred_ne, hpred_nd⟩ hchain hpred_chain T
      (fun s hs ↦ ⟨List.Sublist.mem (hTmem s hs).1
        (List.dropLast_prefix l).sublist, by
          rw [← hpred_tf] at hs
          rwa [List.mem_toFinset] at hs⟩)
      hge
  have hBlt : (B.card : ℝ) < 2 * (C₁ - C₂ + 1) * Real.sqrt n := by
    have : (B.card : ℝ) ≤ T.card := by exact_mod_cast hBT
    linarith
  rw [hBset, Set.ncard_coe_finset]
  exact le_of_lt hBlt

end LongPathStructure

section LongPathStructureMain

/-- `adjXY` is symmetric in its endpoints. -/
private theorem adjXY_symm' {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {X Y : Finset V} {c : Color} {a b : V}
    (h : Color.adjXY G X Y c a b) : Color.adjXY G X Y c b a := by
  cases c
  · rcases h.1 with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact ⟨Or.inr ⟨hy, hx⟩, h.2.symm⟩
    · exact ⟨Or.inl ⟨hx, hy⟩, h.2.symm⟩
  · rcases h.1 with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact ⟨Or.inr ⟨hy, hx⟩, fun hba ↦ h.2 hba.symm⟩
    · exact ⟨Or.inl ⟨hx, hy⟩, fun hba ↦ h.2 hba.symm⟩

/-- `adjXY` is irreflexive when the sides are disjoint. -/
private theorem adjXY_irrefl {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {X Y : Finset V} (hXY : Disjoint X Y) {c : Color} {a : V}
    (h : Color.adjXY G X Y c a a) : False := by
  cases c <;> rcases h.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (Finset.disjoint_left.mp hXY h1) h2
  · exact (Finset.disjoint_left.mp hXY h2) h1
  · exact (Finset.disjoint_left.mp hXY h1) h2
  · exact (Finset.disjoint_left.mp hXY h2) h1

/-- An `acrossXY` pair that is `c`-adjacent is `adjXY`-adjacent. -/
private theorem adjXY_of_across_adj {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {X Y : Finset V} {c : Color} {a b : V}
    (h1 : acrossXY X Y a b) (h2 : Color.adj G c a b) :
    Color.adjXY G X Y c a b := by
  cases c
  · exact ⟨h1, h2⟩
  · exact ⟨h1, h2.2⟩

/-- The `c`-coloured complete bipartite graph between `X` and `Y`. -/
private def adjXYGraph {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {X Y : Finset V} (hXY : Disjoint X Y) (c : Color) : SimpleGraph V where
  Adj := Color.adjXY G X Y c
  symm := ⟨fun _ _ h ↦ adjXY_symm' G h⟩
  loopless := ⟨fun _ h ↦ adjXY_irrefl G hXY h⟩

private theorem adjXYGraph_adj {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {X Y : Finset V} (hXY : Disjoint X Y) (c : Color) (a b : V) :
    (adjXYGraph G hXY c).Adj a b = Color.adjXY G X Y c a b := rfl

/-- Enumerate a finset of paths as a family indexed by `Fin` of its cardinal,
landing in the finset and hitting every member. -/
private theorem enum_path_family {V : Type*} [Fintype V] [DecidableEq V]
    (P_fam : Finset (VertPath V)) :
    ∃ F : Fin P_fam.card → VertPath V,
      (∀ i, F i ∈ P_fam) ∧ (∀ p ∈ P_fam, ∃ i, F i = p) :=
  ⟨fun i ↦ (P_fam.equivFin.symm i).1,
    fun i ↦ (P_fam.equivFin.symm i).2,
    fun _ hp ↦ ⟨P_fam.equivFin ⟨_, hp⟩, by simp⟩⟩

end LongPathStructureMain

set_option maxHeartbeats 1000000 in
/-- **PVW24 Lemma 3.2 (long-path structure).**  If `χ` admits no cover of size
`≤ √n + C₂`, there is a monochromatic path `P` of colour `γ` leaving out few
vertices, such that every outside vertex has at most `2Δ√n` `γ`-neighbours on
`P`, where `Δ = C₁ − C₂ + 1`. -/
theorem long_path_structure {n : ℕ} {C₁ C₂ : ℝ} (hC : C₂ ≤ C₁)
    (hn : 10 ^ 4 * (C₁ - C₂ + 1) ^ 4 < (n : ℝ))
    (hind : ∀ m < n, AllCoverLt m (Real.sqrt m + C₁))
    (G : SimpleGraph (Fin n)) (hG : ¬ HasCoverLe G (Real.sqrt n + C₂)) :
    ∃ c : Color, ∃ P : VertPath (Fin n), P.IsMonochromatic G c ∧
      ((n : ℝ) - P.toList.length ≤ Real.sqrt n + 10 * (C₁ - C₂ + 1) * n ^ ((1 : ℝ) / 4)) ∧
      ∀ y ∉ P.toList,
        (Set.ncard {x : Fin n | x ∈ P.toList ∧ Color.adj G c x y} : ℝ) ≤
          2 * (C₁ - C₂ + 1) * Real.sqrt n := by
  classical
  set Δ := C₁ - C₂ + 1 with hΔdef
  have hΔ : (1 : ℝ) ≤ Δ := by rw [hΔdef]; linarith [hC]
  have hΔpos : (0 : ℝ) < Δ := by linarith
  have hnR : (0 : ℝ) < n := by
    have h1 : (0 : ℝ) < 10 ^ 4 * Δ ^ 4 :=
      mul_pos (by norm_num) (pow_pos hΔpos 4)
    linarith
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hsqrt : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hΔn0 : (0 : ℝ) ≤ 2 * Δ * Real.sqrt n :=
    mul_nonneg (mul_nonneg (by norm_num) hΔpos.le) hsqrt.le
  have hn4pos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hnR _
  -- `√n > 100 Δ²` from `n > 10⁴ Δ⁴`.
  have hsqrt_big : 100 * Δ ^ 2 < Real.sqrt n := by
    have e : ((100 * Δ ^ 2 : ℝ)) ^ 2 < n := by
      have e' : ((100 * Δ ^ 2 : ℝ)) ^ 2 = 10 ^ 4 * Δ ^ 4 := by ring
      linarith [hn]
    have h := Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ (100 * Δ ^ 2) ^ 2) e
    rwa [Real.sqrt_sq (mul_nonneg (by norm_num) (sq_nonneg Δ))] at h
  -- `n^{1/4} > 10 Δ`.
  have hn4 : 10 * Δ < (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have h2 : ((10 * Δ : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = 10 * Δ := by
      have h4 : (10 * Δ : ℝ) ^ 4 = (10 * Δ) ^ ((4 : ℕ) : ℝ) :=
        (Real.rpow_natCast _ 4).symm
      rw [h4, ← Real.rpow_mul (mul_nonneg (by norm_num) hΔpos.le)]
      have e : ((4 : ℕ) : ℝ) * (1 / 4) = 1 := by norm_num
      rw [e, Real.rpow_one]
    rw [← h2, show (10 * Δ : ℝ) ^ 4 = 10 ^ 4 * Δ ^ 4 by ring]
    exact Real.rpow_lt_rpow (by positivity) hn (by norm_num)
  -- `√n = (n^{1/4})²` for later use.
  have hn4sq : ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt n := by
    have h2 : ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 =
        ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ 2).symm
    rw [h2, ← Real.rpow_mul hnR.le, Real.sqrt_eq_rpow]
    have e : (1 : ℝ) / 4 * ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
    rw [e]
  -- Gerencsér–Gyárfás: a monochromatic path covering at least `n/2` vertices.
  haveI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  obtain ⟨γ, Q₀, hQ₀mono, hQ₀len⟩ := exists_mono_path_half G
  rw [Fintype.card_fin] at hQ₀len
  -- Longest `γ`-path `P`.
  obtain ⟨P, hPchain, hPmax⟩ := exists_longest_chain (Color.adj G γ) ⟨0, hn0⟩
  -- Truncate `Q₀` to `t = ⌊n/2⌋` vertices.
  set t := n / 2 with htdef
  have ht0 : 0 < t := by
    have e : (1 : ℝ) ≤ Δ ^ 4 := one_le_pow₀ hΔ
    have h2 : (2 : ℝ) ≤ n := by linarith [hn, e]
    have h2' : 2 ≤ n := by exact_mod_cast h2
    omega
  have htQ : t ≤ Q₀.toList.length := by omega
  set lQ := Q₀.toList.take t with hlQ
  have hlQ_nd : lQ.Nodup := Q₀.nodup.sublist (List.take_sublist t _)
  have hlQ_len : lQ.length = t := by
    rw [hlQ, List.length_take]
    exact min_eq_left htQ
  have hlQ_ne : lQ ≠ [] := by
    intro e
    rw [e, List.length_nil] at hlQ_len
    omega
  set X₀ := lQ.toFinset with hX₀
  have hX₀card : X₀.card = t := by
    rw [hX₀, List.toFinset_card_of_nodup hlQ_nd, hlQ_len]
  have hXc : t ≤ X₀ᶜ.card := by
    rw [Finset.card_compl, hX₀card, Fintype.card_fin]
    omega
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hXc
  have hdisj₀ : Disjoint X₀ W :=
    Finset.disjoint_left.mpr fun a ha hb ↦ (Finset.mem_compl.mp (hWsub hb)) ha
  -- `R` = longest `γ.other`-chain in the bipartite region `X₀ ↔ W`.
  obtain ⟨R, hRchain, hRmax⟩ :=
    exists_longest_chain (Color.adjXY G X₀ W γ.other) ⟨0, hn0⟩
  -- `|R ∩ X₀| < 2Δ√n`, since it is covered by the `γ`-path `lQ` and the
  -- `γ.other`-path `R`.
  set S₀ := R.toList.toFinset ∩ X₀ with hS₀
  have hS₀lt : (S₀.card : ℝ) < 2 * Δ * Real.sqrt n := by
    by_contra hge
    push Not at hge
    have hRmono : R.IsMonochromatic G γ.other :=
      hRchain.imp fun _ _ h ↦ adjXY_to_adj G hdisj₀ h
    have hQmono : (⟨lQ, hlQ_ne, hlQ_nd⟩ : VertPath (Fin n)).IsMonochromatic G γ := by
      show lQ.IsChain (Color.adj G γ)
      exact List.IsChain.take hQ₀mono t
    exact overlap_pair_absurd hC hind hG ⟨lQ, hlQ_ne, hlQ_nd⟩ R hQmono hRmono S₀
      (fun s hs ↦ ⟨by
          rw [hS₀, Finset.mem_inter, hX₀] at hs
          simp only [List.mem_toFinset] at hs
          show s ∈ lQ
          exact hs.2,
        by
          rw [hS₀, Finset.mem_inter] at hs
          simp only [List.mem_toFinset] at hs
          show s ∈ R.toList
          exact hs.1⟩)
      hge
  -- Hence `|R| ≤ k` where `k = 2⌈2Δ√n⌉`.
  set k := 2 * ⌈2 * Δ * Real.sqrt n⌉₊ with hkdef
  have hRlen : R.toList.length < k + 1 := by
    have h1 := alternation_bound G hdisj₀ hRchain R.nodup
    rw [← hS₀] at h1
    have hS0nat : S₀.card < ⌈2 * Δ * Real.sqrt n⌉₊ := by
      rw [Nat.lt_ceil]
      exact hS₀lt
    rw [hkdef]
    omega
  -- `n > 8Δ√n + 5`, since `√n > 100Δ² ≥ 8Δ + 5`.
  have hnbig : (8:ℝ) * Δ * Real.sqrt n + 5 < n := by
    have h85 : (8:ℝ) * Δ + 5 ≤ 100 * Δ ^ 2 := by nlinarith [hΔ]
    have h85' : (8:ℝ) * Δ + 5 < Real.sqrt n := by linarith [h85, hsqrt_big]
    have h1 : Real.sqrt n * (8 * Δ + 5) < n := by
      calc Real.sqrt n * (8 * Δ + 5) < Real.sqrt n * Real.sqrt n :=
            mul_lt_mul_of_pos_left h85' hsqrt
        _ = n := Real.mul_self_sqrt hnR.le
    have h2 : 5 * Real.sqrt n < Real.sqrt n * (8 * Δ + 5) := by
      have h5 : (5:ℝ) < 8 * Δ + 5 := by linarith
      calc 5 * Real.sqrt n < (8 * Δ + 5) * Real.sqrt n :=
            mul_lt_mul_of_pos_right h5 hsqrt
        _ = Real.sqrt n * (8 * Δ + 5) := by ring
    linarith [h1, h2]
  -- `k < n - 1 - k`, so the two `bip_ramsey` parameters are distinct.
  have hkn : k < n - 1 - k := by
    have hkR : (k : ℝ) ≤ 4 * Δ * Real.sqrt n + 2 := by
      rw [hkdef, Nat.cast_mul, Nat.cast_two]
      have hcl := Nat.ceil_lt_add_one hΔn0
      linarith
    have hkn1 : k + 1 + k < n := by
      have : (k : ℝ) + 1 + k < n := by linarith [hkR, hnbig]
      exact_mod_cast this
    omega
  -- `|P| ≥ n − 5Δ√n`, via `bip_ramsey_path` on `X₀ ↔ W`.
  have hPbig : (n : ℝ) - 5 * Δ * Real.sqrt n ≤ P.toList.length := by
    cases γ with
    | red =>
      obtain ⟨p, hp⟩ := bip_ramsey_path G X₀ W hdisj₀
        (k := n - 1 - k) (ℓ := k) (ne_of_gt hkn)
        (by rw [hX₀card, htdef]; omega) (by rw [hWcard, htdef]; omega)
      rcases hp with ⟨hpc, hpl⟩ | ⟨hpc, hpl⟩
      · -- red = γ path on `n − k` vertices.
        have hle := hPmax p (hpc.imp fun _ _ h ↦ adjXY_to_adj G hdisj₀ h)
        have hkR : (k : ℝ) ≤ 5 * Δ * Real.sqrt n := by
          rw [hkdef, Nat.cast_mul, Nat.cast_two]
          have hcl := Nat.ceil_lt_add_one hΔn0
          have h2 : (2 : ℝ) ≤ Δ * Real.sqrt n := by
            nlinarith [hsqrt_big, hΔ,
              mul_le_mul_of_nonneg_right hΔ hsqrt.le]
          linarith
        have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
          rw [Nat.cast_sub (by omega : k ≤ n)]
        have h1 : (n : ℝ) - k ≤ P.toList.length := by
          rw [← hcast]
          have : n - k ≤ p.toList.length := by omega
          exact_mod_cast (le_trans this hle)
        linarith
      · -- blue = γ.other path on `k + 1` vertices: contradiction with `R`.
        have hle := hRmax p hpc
        omega
    | blue =>
      obtain ⟨p, hp⟩ := bip_ramsey_path G X₀ W hdisj₀
        (k := k) (ℓ := n - 1 - k) (ne_of_lt hkn)
        (by rw [hX₀card, htdef]; omega) (by rw [hWcard, htdef]; omega)
      rcases hp with ⟨hpc, hpl⟩ | ⟨hpc, hpl⟩
      · -- red = γ.other path on `k + 1` vertices: contradiction.
        have hle := hRmax p hpc
        omega
      · -- blue = γ path on `n − k` vertices.
        have hle := hPmax p (hpc.imp fun _ _ h ↦ adjXY_to_adj G hdisj₀ h)
        have hkR : (k : ℝ) ≤ 5 * Δ * Real.sqrt n := by
          rw [hkdef, Nat.cast_mul, Nat.cast_two]
          have hcl := Nat.ceil_lt_add_one hΔn0
          have h2 : (2 : ℝ) ≤ Δ * Real.sqrt n := by
            nlinarith [hsqrt_big, hΔ,
              mul_le_mul_of_nonneg_right hΔ hsqrt.le]
          linarith
        have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
          rw [Nat.cast_sub (by omega : k ≤ n)]
        have h1 : (n : ℝ) - k ≤ P.toList.length := by
          rw [← hcast]
          have : n - k ≤ p.toList.length := by omega
          exact_mod_cast (le_trans this hle)
        linarith
  -- `X` = vertex set of `P`, `Y` = its complement.
  set X := P.toList.toFinset with hX
  set Y := Xᶜ with hY
  have hXcard : X.card = P.toList.length := by
    rw [hX, List.toFinset_card_of_nodup P.nodup]
  have hXlen : X.card ≤ n := by
    rw [hXcard]
    exact le_trans P.nodup.length_le_card (le_of_eq (Fintype.card_fin n))
  have hYcard : Y.card = n - X.card := by
    rw [hY, Finset.card_compl, hXcard, Fintype.card_fin]
  have hYb : (Y.card : ℝ) ≤ 5 * Δ * Real.sqrt n := by
    have hcast : ((n - X.card : ℕ) : ℝ) = (n : ℝ) - X.card := by
      rw [Nat.cast_sub hXlen]
    have : ((n - X.card : ℕ) : ℝ) ≤ 5 * Δ * Real.sqrt n := by
      rw [hcast, hXcard]
      linarith [hPbig]
    rw [hYcard]
    exact_mod_cast this
  have hdisjXY : Disjoint X Y :=
    Finset.disjoint_left.mpr fun a ha hb ↦ (Finset.mem_compl.mp hb) ha
  -- The monochromatic `γ`-path and the neighbour bound, valid in all cases.
  have hPmono : P.IsMonochromatic G γ := hPchain
  have hNbrs : ∀ y ∉ P.toList,
      (Set.ncard {x : Fin n | x ∈ P.toList ∧ Color.adj G γ x y} : ℝ) ≤
        2 * (C₁ - C₂ + 1) * Real.sqrt n := by
    intro y hy
    exact few_nbrs_on_path hC hind hG hn0 hPchain P.nodup hPmax hy
  -- If `Y` is empty the leftover bound is trivial.
  by_cases hYe : Y = ∅
  · have hY0 : (Y.card : ℝ) = 0 := by rw [hYe]; simp
    have hnil : (n : ℝ) - P.toList.length = 0 := by
      rw [hYcard] at hY0
      have hcast : ((n - X.card : ℕ) : ℝ) = (n : ℝ) - X.card := Nat.cast_sub hXlen
      rw [hcast, hXcard] at hY0
      linarith
    exact ⟨γ, P, hPmono, by
        rw [hnil]
        linarith [hsqrt.le, mul_pos hΔpos hn4pos],
      hNbrs⟩
  · -- `Y ≠ ∅`: run the bipartite covering argument.
    have hYne : Y.Nonempty := Finset.nonempty_iff_ne_empty.mpr hYe
    have hYpos' : 0 < Y.card := Finset.card_pos.mpr hYne
    have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast hYpos'
    generalize hmdef : ⌊2 * Δ * Real.sqrt n⌋₊ = m
    -- Every `y ∈ Y` has at least `|X| − m` `γ.other`-neighbours in `X`.
    have hdegN : ∀ y ∈ Y, X.card - m ≤
        (X.filter fun x ↦ Color.adj G γ.other x y).card := by
      intro y hy
      have hyX : y ∉ X := (Finset.mem_compl.mp hy)
      have hyl : y ∉ P.toList := by
        intro hyl
        exact hyX (by rw [hX, List.mem_toFinset]; exact hyl)
      have hB := few_nbrs_on_path hC hind hG hn0 hPchain P.nodup hPmax hyl
      set B := X.filter (fun x ↦ Color.adj G γ x y) with hBdef
      have hBset : {x : Fin n | x ∈ P.toList ∧ Color.adj G γ x y} = (B : Set (Fin n)) := by
        ext x
        simp [hBdef, hX, Finset.coe_filter, List.mem_toFinset]
      rw [hBset, Set.ncard_coe_finset] at hB
      have hBm : B.card ≤ m := by
        rw [← hmdef]
        exact Nat.le_floor hB
      have hsplit : X = B ∪ (X.filter fun x ↦ Color.adj G γ.other x y) := by
        ext x
        simp only [hBdef, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hxX
          have hxy : x ≠ y := by
            intro e
            subst e
            exact hyX hxX
          rcases Color.adj_or_adj_other G hxy with h | h
          · exact Or.inl ⟨hxX, h⟩
          · exact Or.inr ⟨hxX, h⟩
        · rintro (⟨hxX, -⟩ | ⟨hxX, -⟩)
          · exact hxX
          · exact hxX
      have hcard_union : X.card ≤ B.card +
          (X.filter fun x ↦ Color.adj G γ.other x y).card := by
        calc X.card = (B ∪ (X.filter fun x ↦ Color.adj G γ.other x y)).card :=
              congrArg Finset.card hsplit
          _ ≤ B.card + (X.filter fun x ↦ Color.adj G γ.other x y).card :=
              Finset.card_union_le _ _
      omega
    -- The auxiliary bipartite `γ.other` graph.
    set H := adjXYGraph G hdisjXY γ.other with hH
    have hbip : BipartiteOn H X Y :=
      ⟨hdisjXY, fun a b h ↦ bip_ramsey_path.Color.adjXY.across
        (show Color.adjXY G X Y γ.other a b from h)⟩
    have hdeg : ∀ y ∈ Y, (H.neighborFinset y).card ≥ X.card - m := by
      intro y hy
      have hsub : (X.filter fun x ↦ Color.adj G γ.other x y) ⊆ H.neighborFinset y := by
        intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hxX, hadj⟩ := hx
        rw [SimpleGraph.mem_neighborFinset]
        show Color.adjXY G X Y γ.other y x
        exact adjXY_of_across_adj G (Or.inr ⟨hy, hxX⟩) (Color.adj_symm G hadj)
      calc X.card - m ≤ (X.filter fun x ↦ Color.adj G γ.other x y).card :=
            hdegN y hy
        _ ≤ (H.neighborFinset y).card := Finset.card_le_card hsub
    have hcardXY : Y.card + 2 * m ≤ X.card := by
      have hmR : (m : ℝ) ≤ 2 * Δ * Real.sqrt n := by
        rw [← hmdef]
        exact Nat.floor_le hΔn0
      have hXR : (X.card : ℝ) ≥ (n : ℝ) - 5 * Δ * Real.sqrt n := by
        rw [hXcard]
        exact hPbig
      have : (Y.card : ℝ) + 2 * m ≤ X.card := by
        have h14 : (14 : ℝ) * Δ * Real.sqrt n < n := by
          have h14' : (14 : ℝ) * Δ < Real.sqrt n := by
            have hge : (14 : ℝ) * Δ ≤ 100 * Δ ^ 2 := by nlinarith [hΔ]
            linarith
          calc (14:ℝ) * Δ * Real.sqrt n < Real.sqrt n * Real.sqrt n :=
                mul_lt_mul_of_pos_right h14' hsqrt
            _ = n := Real.mul_self_sqrt hnR.le
        nlinarith [hYb, hmR, hXR, h14]
      exact_mod_cast this
    -- `14Δ√n < n`, reused below to show the overlap set is nonempty.
    have h14 : (14 : ℝ) * Δ * Real.sqrt n < n := by
      have h14' : (14 : ℝ) * Δ < Real.sqrt n := by
        have hge : (14 : ℝ) * Δ ≤ 100 * Δ ^ 2 := by nlinarith [hΔ]
        linarith
      calc (14:ℝ) * Δ * Real.sqrt n < Real.sqrt n * Real.sqrt n :=
            mul_lt_mul_of_pos_right h14' hsqrt
        _ = n := Real.mul_self_sqrt hnR.le
    obtain ⟨P_fam, hPf_chain, hPf_mem, hPf_cov, hPf_card, hPf_uncov⟩ :=
      few_paths_of_min_degree H X Y m hbip hYpos' hcardXY hdeg
    obtain ⟨Pf, hPf_mem_fam, hPf_surj⟩ := enum_path_family P_fam
    have hPfmono : ∀ i, (Pf i).IsMonochromatic G γ.other := fun i ↦
      (hPf_chain (Pf i) (hPf_mem_fam i)).imp fun _ _ h ↦
        adjXY_to_adj G hdisjXY h
    -- The set `S` of `X`-vertices covered by the `γ.other` path family.
    generalize hTdef : P_fam.biUnion VertPath.verts = T
    generalize hSdef : X ∩ T = S
    have hXT : (X \ T).card ≤ Y.card + 2 * m := by
      rw [← hTdef]
      exact hPf_uncov
    have hS_eq : S = X \ (X \ T) := by
      rw [← hSdef]
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      constructor
      · rintro ⟨hX, hT⟩
        exact ⟨hX, fun ⟨_, hnT⟩ ↦ hnT hT⟩
      · rintro ⟨hX, hnXT⟩
        exact ⟨hX, not_not.mp fun hT ↦ hnXT ⟨hX, hT⟩⟩
    have hSeq : S.card = X.card - (X \ T).card := by
      rw [hS_eq]
      exact Finset.card_sdiff_of_subset Finset.sdiff_subset
    have hScard : X.card - (Y.card + 2 * m) ≤ S.card := by omega
    have h2Ym : (2 : ℝ) * Y.card + 2 * m < n := by
      have hmR : (m : ℝ) ≤ 2 * Δ * Real.sqrt n := by
        rw [← hmdef]
        exact Nat.floor_le hΔn0
      linarith [hYb, hmR, h14]
    have h2Ym' : 2 * Y.card + 2 * m < n := by exact_mod_cast h2Ym
    have hSne : S.Nonempty := by
      have hSpos : 0 < S.card := by omega
      exact Finset.card_pos.mp hSpos
    have hPf_pos : 0 < P_fam.card := by
      rcases hSne with ⟨s, hs⟩
      rw [← hSdef, Finset.mem_inter, ← hTdef, Finset.mem_biUnion] at hs
      obtain ⟨-, p, hp, -⟩ := hs
      exact Finset.card_pos.mpr ⟨p, hp⟩
    have hSX : ∀ s ∈ S, s ∈ P := by
      intro s hs
      rw [← hSdef, Finset.mem_inter] at hs
      show s ∈ P.toList
      rw [← List.mem_toFinset, ← hX]
      exact hs.1
    have hST : ∀ s ∈ S, ∃ i, s ∈ Pf i := by
      intro s hs
      rw [← hSdef, Finset.mem_inter, ← hTdef, Finset.mem_biUnion] at hs
      obtain ⟨-, p, hp, hsp⟩ := hs
      obtain ⟨i, hi⟩ := hPf_surj p hp
      exact ⟨i, VertPath.mem_verts.mp (hi.symm ▸ hsp)⟩
    -- `overlap_bound` contrapositive: `√(n−|S|) + C₁ + |Pf| > √n + C₂`.
    have hgt : Real.sqrt n + C₂ <
        Real.sqrt ((n : ℝ) - S.card) + C₁ + P_fam.card := by
      by_contra hle
      push Not at hle
      cases γ with
      | red =>
        exact hG (overlap_bound hind G
          (fun _ : Fin P_fam.card ↦ P) (fun _ ↦ hPmono)
          Pf hPfmono S hSne
          (fun s hs ↦ ⟨⟨⟨0, hPf_pos⟩, hSX s hs⟩, hST s hs⟩) hle)
      | blue =>
        exact hG (overlap_bound hind G
          Pf hPfmono
          (fun _ : Fin P_fam.card ↦ P) (fun _ ↦ hPmono) S hSne
          (fun s hs ↦ ⟨hST s hs, ⟨⟨0, hPf_pos⟩, hSX s hs⟩⟩) hle)
    -- `√(n−|S|) ≤ √(2|Y|+2m) ≤ 4Δ n^{1/4}`.
    have hnsub : (n : ℝ) - S.card ≤ 2 * Y.card + 2 * m := by
      have hXYc : (X.card : ℝ) + Y.card = n := by
        rw [hYcard, Nat.cast_sub hXlen]
        ring
      have hSc : (S.card : ℝ) ≥ (n : ℝ) - 2 * Y.card - 2 * m := by
        have : (S.card : ℝ) = X.card - (X \ T).card := by
          rw [hSeq, Nat.cast_sub (Finset.card_le_card Finset.sdiff_subset)]
        rw [this]
        have hXTR : ((X \ T).card : ℝ) ≤ Y.card + 2 * m := by exact_mod_cast hXT
        linarith
      calc (n : ℝ) - S.card
          ≤ (n : ℝ) - ((n : ℝ) - 2 * Y.card - 2 * m) := sub_le_sub_left hSc _
        _ = 2 * Y.card + 2 * m := by ring
    have hsqrtS : Real.sqrt ((n : ℝ) - S.card) ≤
        Real.sqrt (2 * Y.card + 2 * m) :=
      Real.sqrt_le_sqrt hnsub
    have hsqrt14 : Real.sqrt (2 * (Y.card : ℝ) + 2 * m) ≤
        4 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      have hmR : (m : ℝ) ≤ 2 * Δ * Real.sqrt n := by
        rw [← hmdef]
        exact Nat.floor_le hΔn0
      have harg : (2:ℝ) * Y.card + 2 * m ≤ 14 * Δ * Real.sqrt n := by
        linarith [hYb, hmR]
      have hnonneg : (0 : ℝ) ≤ 4 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4) := by
        have h := mul_nonneg hΔpos.le hn4pos.le
        linarith
      rw [Real.sqrt_le_left hnonneg]
      have hsq' : (4 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 =
          16 * Δ ^ 2 * Real.sqrt n := by
        rw [mul_pow, hn4sq]
        ring
      rw [hsq']
      nlinarith [harg, hΔ, hsqrt,
        mul_nonneg (show (0 : ℝ) ≤ 16 * Δ ^ 2 - 14 * Δ by nlinarith [hΔ]) hsqrt.le]
    -- `|Pf| ≤ |X|/|Y| ≤ n/|Y|`.
    have hPfcard : (P_fam.card : ℝ) ≤ (n : ℝ) / Y.card := by
      calc (P_fam.card : ℝ) ≤ ((X.card / Y.card : ℕ) : ℝ) := by
            exact_mod_cast hPf_card
        _ ≤ (X.card : ℝ) / Y.card := Nat.cast_div_le
        _ ≤ (n : ℝ) / Y.card := by
            apply div_le_div_of_nonneg_right _ hYpos.le
            exact_mod_cast hXlen
    have key : Real.sqrt n + C₂ <
        4 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4) + C₁ + (n : ℝ) / Y.card := by
      linarith [hgt, hsqrtS, hsqrt14, hPfcard]
    -- Final arithmetic: `|Y| < √n + 10Δ n^{1/4}`.
    have hn4ge1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.one_le_rpow (by exact_mod_cast hn0) (by norm_num)
    have hC12 : C₁ - C₂ = Δ - 1 := by rw [hΔdef]; ring
    have hdenom : (0 : ℝ) <
        Real.sqrt n - 5 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← hn4sq]
      have ha10 : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) - 10 * Δ := by linarith [hn4]
      nlinarith [mul_pos hn4pos ha10, mul_pos hΔpos hn4pos]
    have h' : Real.sqrt n - 5 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4) <
        (n : ℝ) / Y.card := by
      linarith [key, hC12,
        mul_nonneg hΔpos.le (show (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) - 1 by
          linarith [hn4ge1])]
    have hmul : (Real.sqrt n - 5 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4)) *
        (Y.card : ℝ) < n :=
      (lt_div_iff₀ hYpos).mp h'
    have hprod : (n : ℝ) <
        (Real.sqrt n - 5 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4)) *
          (Real.sqrt n + 10 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4)) := by
      have e : (Real.sqrt n - 5 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4)) *
          (Real.sqrt n + 10 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4)) =
          Real.sqrt n ^ 2 + 5 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt n -
            50 * Δ ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
        ring
      rw [e, Real.sq_sqrt hnR.le]
      have ha2 : (0 : ℝ) < ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := pow_pos hn4pos 2
      have ha10 : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) - 10 * Δ := by linarith [hn4]
      have h3 := mul_pos (mul_pos hΔpos ha2) ha10
      -- `5Δa³ − 50Δ²a² = 5Δa²(a − 10Δ) > 0`, rewriting `√n = a²`.
      rw [← hn4sq]
      nlinarith [h3]
    have hYlt : (Y.card : ℝ) <
        Real.sqrt n + 10 * Δ * (n : ℝ) ^ ((1 : ℝ) / 4) :=
      lt_of_mul_lt_mul_left (lt_trans hmul hprod) (le_of_lt hdenom)
    have hleft : (n : ℝ) - P.toList.length = Y.card := by
      rw [← hXcard, hYcard, Nat.cast_sub hXlen]
    exact ⟨γ, P, hPmono, by rw [hleft]; linarith [hYlt], hNbrs⟩

section TailPairing

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- Build a blue path `ya — a ⋯ b — yb` through an infix `a :: m ++ [b]` of a
blue chain `l`, where `ya, yb` are fresh vertices (off `l`, distinct) that are
blue-adjacent to the endpoints `a, b`.  This is the pair path of Lemma 3.3:
the interior is a segment of `P`, so it may share vertices with `P` — covers
need not be disjoint. -/
private theorem mk_pair_path {l : List (Fin n)}
    (hnodup : l.Nodup) {m : List (Fin n)} {ya yb a b : Fin n}
    (hinfix : (a :: m ++ [b]) <:+: l)
    (hm : (a :: m ++ [b]).IsChain (Color.adj G .blue))
    (hya : ya ∉ l) (hyb : yb ∉ l) (hyy : ya ≠ yb)
    (ha : Color.adj G .blue ya a) (hb : Color.adj G .blue b yb) :
    ∃ p : VertPath (Fin n), p.IsMonochromatic G .blue ∧ ya ∈ p.toList ∧
      yb ∈ p.toList := by
  have hsub := hinfix.sublist
  have hmn : (a :: m ++ [b]).Nodup := hnodup.sublist hsub
  refine ⟨⟨ya :: (a :: m ++ [b]) ++ [yb], by simp, ?_⟩, ?_, ?_, ?_⟩
  · -- Nodup: `ya`, `yb` are fresh and distinct, the interior is nodup.
    rw [List.nodup_append, List.nodup_cons]
    refine ⟨⟨?_, hmn⟩, List.nodup_singleton yb, ?_⟩
    · intro hmem
      exact hya (hsub.mem hmem)
    · intro x hx y hy
      rw [List.mem_singleton] at hy
      subst hy
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hyy
      · exact fun h => hyb (h ▸ hsub.mem hx)
  · -- IsChain: boundary edges `ya—a` and `b—yb` are blue.
    refine List.IsChain.append ?_ (List.isChain_singleton yb) ?_
    · refine hm.cons (fun y hy => ?_)
      have hd : (a :: m ++ [b]).head? = some a := by
        simp
      rw [hd, Option.mem_some] at hy
      subst y
      exact ha
    · intro x hx y hy
      rw [List.head?_cons, Option.mem_some] at hy
      have hx' : (ya :: (a :: m ++ [b])).getLast? = some b := by
        rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_concat]
      rw [hx', Option.mem_some] at hx
      subst x
      subst y
      exact hb
  · show ya ∈ ya :: (a :: m ++ [b]) ++ [yb]
    exact List.mem_append_left _ List.mem_cons_self
  · show yb ∈ ya :: (a :: m ++ [b]) ++ [yb]
    exact List.mem_append_right _ (List.mem_singleton_self yb)

/-- Two fresh vertices `y₁ y₂` with prescribed blue neighbours `u v` on a blue
chain `l` are joined by a single blue path through a segment of `l`. -/
private theorem pair_path {l : List (Fin n)}
    (hchain : l.IsChain (Color.adj G .blue)) (hnodup : l.Nodup)
    {y₁ y₂ u v : Fin n} (hy1 : y₁ ∉ l) (hy2 : y₂ ∉ l) (hyy : y₁ ≠ y₂)
    (hu : u ∈ l) (hv : v ∈ l)
    (h1 : Color.adj G .blue u y₁) (h2 : Color.adj G .blue v y₂) :
    ∃ p : VertPath (Fin n), p.IsMonochromatic G .blue ∧ y₁ ∈ p.toList ∧
      y₂ ∈ p.toList := by
  obtain ⟨as, bs, rfl, -⟩ := List.eq_append_cons_of_mem hu
  by_cases hv' : v ∈ as
  · -- `v` occurs before `u`: the segment is `v :: bs' ++ [u]`.
    obtain ⟨as', bs', rfl, -⟩ := List.eq_append_cons_of_mem hv'
    have hinfix : (v :: bs' ++ [u]) <:+: (as' ++ v :: bs') ++ u :: bs :=
      ⟨as', bs, by simp [List.append_assoc]⟩
    obtain ⟨p, hp, hp1, hp2⟩ := mk_pair_path G hnodup hinfix
      (hchain.infix hinfix) hy2 hy1 hyy.symm (Color.adj_symm G h2) h1
    exact ⟨p, hp, hp2, hp1⟩
  · have hvmem : v ∈ u :: bs := by
      have h := hv
      rw [List.mem_append] at h
      exact h.resolve_left hv'
    rw [List.mem_cons] at hvmem
    rcases hvmem with huv | hvb
    · -- `u = v`: the three-vertex path `y₁ u y₂`.
      have h2' : Color.adj G .blue u y₂ := huv ▸ h2
      refine ⟨⟨[y₁, u, y₂], by simp, ?_⟩, ?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
          List.nodup_singleton y₂⟩⟩
        · rw [List.mem_cons, List.mem_singleton]
          exact fun h => h.elim (fun h => hy1 (h ▸ hu)) hyy
        · rw [List.mem_singleton]
          exact fun h => hy2 (h ▸ hu)
      · exact List.isChain_cons_cons.mpr ⟨Color.adj_symm G h1,
          List.isChain_pair.mpr h2'⟩
      · show y₁ ∈ [y₁, u, y₂]
        simp
      · show y₂ ∈ [y₁, u, y₂]
        simp
    · -- `v` occurs after `u`: the segment is `u :: bs' ++ [v]`.
      obtain ⟨bs', ds, rfl, -⟩ := List.eq_append_cons_of_mem hvb
      have hinfix : (u :: bs' ++ [v]) <:+: as ++ u :: (bs' ++ v :: ds) :=
        ⟨as, ds, by simp [List.append_assoc]⟩
      exact mk_pair_path G hnodup hinfix (hchain.infix hinfix) hy1 hy2 hyy
        (Color.adj_symm G h1) h2

/-- Inductive pairing: any set `S` of vertices off `P`, each having a blue
neighbour on `P`, is covered by at most `⌈|S|/2⌉` blue paths (each covering
one or two vertices of `S`). -/
private theorem pair_family
    (P : VertPath (Fin n)) (hP : P.IsMonochromatic G .blue)
    (S : Finset (Fin n))
    (hS : ∀ y ∈ S, y ∉ P.toList ∧ ∃ x ∈ P.toList, Color.adj G .blue x y) :
    ∃ F : Finset (VertPath (Fin n)),
      (∀ p ∈ F, p.IsMonochromatic G .blue) ∧
      (∀ y ∈ S, ∃ p ∈ F, y ∈ p) ∧
      F.card ≤ (S.card + 1) / 2 := by
  classical
  revert hS
  refine Finset.strongInductionOn S (p := fun T =>
    (∀ y ∈ T, y ∉ P.toList ∧ ∃ x ∈ P.toList, Color.adj G .blue x y) →
    ∃ F : Finset (VertPath (Fin n)),
      (∀ p ∈ F, p.IsMonochromatic G .blue) ∧
      (∀ y ∈ T, ∃ p ∈ F, y ∈ p) ∧
      F.card ≤ (T.card + 1) / 2) (fun T ihT hT => ?_)
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, fun p hp => by simp at hp,
      fun y hy => by simp at hy, by simp⟩
  · obtain ⟨y₁, hy₁⟩ := hne
    obtain ⟨hy₁P, x₁, hx₁P, hax₁⟩ := hT y₁ hy₁
    rcases (T.erase y₁).eq_empty_or_nonempty with hE | hne'
    · -- `T = {y₁}`: one singleton path.
      have hT1 : T = {y₁} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨hy₁, fun y hy => ?_⟩
        by_contra h
        have hmem : y ∈ (∅ : Finset (Fin n)) := hE ▸ Finset.mem_erase.mpr ⟨h, hy⟩
        simp at hmem
      refine ⟨{VertPath.singleton y₁}, ?_, ?_, ?_⟩
      · intro p hp
        rw [Finset.mem_singleton] at hp
        rw [hp]
        exact List.isChain_singleton y₁
      · intro y hy
        rw [hT1, Finset.mem_singleton] at hy
        exact ⟨VertPath.singleton y₁, Finset.mem_singleton_self _,
          VertPath.mem_singleton.mpr hy⟩
      · have hcard : T.card = 1 := by rw [hT1, Finset.card_singleton]
        rw [Finset.card_singleton]
        omega
    · -- Pair `y₁` with `y₂` through a segment of `P`, then recurse.
      obtain ⟨y₂, hy₂⟩ := hne'
      have hy₂T : y₂ ∈ T := Finset.mem_of_mem_erase hy₂
      have hyy : y₁ ≠ y₂ := fun h => (Finset.mem_erase.mp hy₂).1 h.symm
      obtain ⟨hy₂P, x₂, hx₂P, hax₂⟩ := hT y₂ hy₂T
      obtain ⟨q, hqmono, hqy1, hqy2⟩ :=
        pair_path G hP P.nodup hy₁P hy₂P hyy hx₁P hx₂P hax₁ hax₂
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨y₁, hy₁⟩
      have hc1 : (T.erase y₁).card = T.card - 1 := Finset.card_erase_of_mem hy₁
      have hc2 : ((T.erase y₁).erase y₂).card = (T.erase y₁).card - 1 :=
        Finset.card_erase_of_mem hy₂
      have hsub : (T.erase y₁).erase y₂ ⊂ T :=
        lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hy₁)
      obtain ⟨F', hF'mono, hF'cov, hF'card⟩ :=
        ihT _ hsub (fun y hy => hT y
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)))
      refine ⟨insert q F', ?_, ?_, ?_⟩
      · intro p hp
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact hqmono
        · exact hF'mono p hp
      · intro y hy
        by_cases hyT : y ∈ (T.erase y₁).erase y₂
        · obtain ⟨p, hp, hpy⟩ := hF'cov y hyT
          exact ⟨p, Finset.mem_insert_of_mem hp, hpy⟩
        · have hy12 : y = y₁ ∨ y = y₂ := by
            by_contra h
            push Not at h
            exact hyT (Finset.mem_erase.mpr
              ⟨h.2, Finset.mem_erase.mpr ⟨h.1, hy⟩⟩)
          rcases hy12 with rfl | rfl
          · exact ⟨q, Finset.mem_insert_self _ _, hqy1⟩
          · exact ⟨q, Finset.mem_insert_self _ _, hqy2⟩
      · calc (insert q F').card ≤ F'.card + 1 := Finset.card_insert_le _ _
          _ ≤ (T.card + 1) / 2 := by omega

end TailPairing

/-- **PVW24 Lemma 3.3 (tail pairing).**  If `P` is a blue path, `Y = [n] ∖ V(P)`
and `Y₀ ⊆ Y` is the set of leftover vertices with no blue edge to `P`, then
`f(n,χ) < 2 + |Y|/2 + |Y₀|/2` (in fact `f ≤ 1 + ⌈|Y ∖ Y₀|/2⌉ + |Y₀|`). -/
theorem tail_pairing_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (P : VertPath (Fin n)) (hP : P.IsMonochromatic G .blue)
    (Y Y₀ : Finset (Fin n))
    (hY : ∀ y, y ∈ Y ↔ y ∉ P.toList)
    (hY0 : ∀ y, y ∈ Y₀ ↔ y ∉ P.toList ∧ ∀ x ∈ P.toList, ¬ Color.adj G .blue x y) :
    HasCoverLt G (2 + (Y.card : ℝ) / 2 + (Y₀.card : ℝ) / 2) := by
  classical
  have hY0sub : Y₀ ⊆ Y := fun y hy => (hY y).mpr ((hY0 y).mp hy).1
  -- Every `y ∈ Y ∖ Y₀` has a blue neighbour on `P`.
  have hS : ∀ y ∈ Y \ Y₀, y ∉ P.toList ∧
      ∃ x ∈ P.toList, Color.adj G .blue x y := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    have hyP : y ∉ P.toList := (hY y).mp hy.1
    refine ⟨hyP, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hy.2 ((hY0 y).mpr ⟨hyP, hcon⟩)
  obtain ⟨F, hFmono, hFcov, hFcard⟩ := pair_family G P hP (Y \ Y₀) hS
  -- The cover: `P`, the pair paths for `Y ∖ Y₀`, and singletons for `Y₀`.
  refine ⟨.blue, insert P (F ∪ Y₀.map VertPath.singletonEmbedding),
    ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · exact hP
    · rw [Finset.mem_union] at hq
      rcases hq with hq | hq
      · exact hFmono q hq
      · obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hq
        exact List.isChain_singleton y
  · intro v
    by_cases hvP : v ∈ P.toList
    · exact ⟨P, Finset.mem_insert_self _ _, hvP⟩
    · have hvY : v ∈ Y := (hY v).mpr hvP
      by_cases hv0 : v ∈ Y₀
      · refine ⟨VertPath.singletonEmbedding v,
          Finset.mem_insert_of_mem (Finset.mem_union_right _
            (Finset.mem_map.mpr ⟨v, hv0, rfl⟩)), ?_⟩
        exact VertPath.mem_singleton.mpr rfl
      · have hv1 : v ∈ Y \ Y₀ := Finset.mem_sdiff.mpr ⟨hvY, hv0⟩
        obtain ⟨q, hq, hvq⟩ := hFcov v hv1
        exact ⟨q, Finset.mem_insert_of_mem (Finset.mem_union_left _ hq), hvq⟩
  · -- `|cover| ≤ 1 + ⌈|Y₁|/2⌉ + |Y₀| < 2 + |Y|/2 + |Y₀|/2`.
    have hY1 : ((Y \ Y₀).card : ℝ) + Y₀.card = Y.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hY0sub
    have hc : (insert P (F ∪ Y₀.map VertPath.singletonEmbedding)).card ≤
        ((Y \ Y₀).card + 1) / 2 + 1 + Y₀.card := by
      calc (insert P (F ∪ Y₀.map VertPath.singletonEmbedding)).card
          ≤ (F ∪ Y₀.map VertPath.singletonEmbedding).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ F.card + Y₀.card + 1 := by
            have h1 := Finset.card_union_le F
              (Y₀.map VertPath.singletonEmbedding)
            rw [Finset.card_map] at h1
            omega
        _ ≤ ((Y \ Y₀).card + 1) / 2 + 1 + Y₀.card := by omega
    have h1 : ((((Y \ Y₀).card + 1) / 2 : ℕ) : ℝ) ≤ (((Y \ Y₀).card : ℝ) + 1) / 2 := by
      have h := Nat.cast_div_le (m := (Y \ Y₀).card + 1) (n := 2) (α := ℝ)
      push_cast at h
      exact h
    have h2 : ((insert P (F ∪ Y₀.map VertPath.singletonEmbedding)).card : ℝ) ≤
        ((((Y \ Y₀).card + 1) / 2 : ℕ) : ℝ) + 1 + Y₀.card := by
      have h3 : ((insert P (F ∪ Y₀.map VertPath.singletonEmbedding)).card : ℝ) ≤
          ((((Y \ Y₀).card + 1) / 2 + 1 + Y₀.card : ℕ) : ℝ) := by
        exact_mod_cast hc
      rwa [Nat.cast_add, Nat.cast_add, Nat.cast_one] at h3
    linarith

/-- **PVW24 Proposition 3.4 (weak bound).**  For all `n`,
`f(n) < √n + 20⁴`. -/
theorem weak_sqrt_bound (n : ℕ) :
    AllCoverLt n (Real.sqrt n + 20 ^ 4) := by
  sorry

/-- **PVW24 Theorem 1.3 — the Erdős–Gyárfás conjecture.**  For all
`n > 20^{40}`, every 2-edge-coloured `K_n` has a vertex cover by at most `√n`
monochromatic paths, all of the same colour. -/
theorem monochromatic_path_cover {n : ℕ} (hn : 20 ^ 40 < n)
    (G : SimpleGraph (Fin n)) :
    ∃ c : Color, ∃ P : Finset (VertPath (Fin n)),
      IsSameColorCover G c P ∧ (P.card : ℝ) ≤ Real.sqrt n := by
  sorry

end JSP415
