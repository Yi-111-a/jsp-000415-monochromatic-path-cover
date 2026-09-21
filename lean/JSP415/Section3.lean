import JSP415.Defs
import JSP415.Gerencser
import JSP415.BipCover
import JSP415.BipRamsey

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

/-- In the complement graph `Gᶜ`, blue adjacency is red adjacency. -/
private theorem compl_blue_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {a b : V} : Color.adj Gᶜ .blue a b ↔ Color.adj G .red a b := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨h.ne, fun hc ↦ ?_⟩⟩
  · by_contra hna
    exact h.2 ((SimpleGraph.compl_adj _ _ _).mpr ⟨h.1, hna⟩)
  · exact ((SimpleGraph.compl_adj _ _ _).mp hc).2 h

/-- In the complement graph, red adjacency is blue adjacency. -/
private theorem compl_red_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {a b : V} : Color.adj Gᶜ .red a b ↔ Color.adj G .blue a b :=
  SimpleGraph.compl_adj _ _ _

/-- A monochromatic cover of `Gᶜ` is a monochromatic cover of `G`. -/
private theorem HasCoverLt.of_compl {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {b : ℝ} (h : HasCoverLt Gᶜ b) : HasCoverLt G b := by
  obtain ⟨c, F, ⟨hmono, hcov⟩, hcard⟩ := h
  cases c with
  | red =>
    exact ⟨.blue, F, ⟨fun p hp ↦ (hmono p hp).imp fun _ _ hab ↦
      (compl_red_iff G).mp hab, hcov⟩, hcard⟩
  | blue =>
    exact ⟨.red, F, ⟨fun p hp ↦ (hmono p hp).imp fun _ _ hab ↦
      (compl_blue_iff G).mp hab, hcov⟩, hcard⟩

/-- `tail_pairing_bound` for a monochromatic path of either color.
For a red path we apply the lemma in `Gᶜ`. -/
private theorem tail_pairing_bound_color {n : ℕ} (G : SimpleGraph (Fin n))
    (P : VertPath (Fin n)) {γ : Color} (hP : P.IsMonochromatic G γ)
    (Y Y₀ : Finset (Fin n))
    (hY : ∀ y, y ∈ Y ↔ y ∉ P.toList)
    (hY0 : ∀ y, y ∈ Y₀ ↔ y ∉ P.toList ∧ ∀ x ∈ P.toList, ¬ Color.adj G γ x y) :
    HasCoverLt G (2 + (Y.card : ℝ) / 2 + (Y₀.card : ℝ) / 2) := by
  cases γ with
  | blue => exact tail_pairing_bound G P hP Y Y₀ hY hY0
  | red =>
    have hP' : P.IsMonochromatic Gᶜ .blue :=
      hP.imp fun _ _ h ↦ (compl_blue_iff G).mpr h
    have hY0' : ∀ y, y ∈ Y₀ ↔
        y ∉ P.toList ∧ ∀ x ∈ P.toList, ¬ Color.adj Gᶜ .blue x y := by
      intro y
      rw [hY0 y]
      exact Iff.and Iff.rfl (forall_congr' fun x ↦ forall_congr' fun _ ↦
        not_congr (compl_blue_iff G).symm)
    exact HasCoverLt.of_compl G (tail_pairing_bound Gᶜ P hP' Y Y₀ hY hY0')

/-- Alternating-path construction.  Given disjoint nodup lists `xs` and
`ys` with `|ys| = |xs| + 1`, where every `x ∈ xs` is `R`-related to every
`y ∈ ys`, the list `y₀ x₁ y₁ ⋯ x_t y_t` is an `R`-chain covering `xs`.
Built by induction on `xs`. -/
private theorem alt_path_list {n : ℕ} {R : Fin n → Fin n → Prop}
    (hR : ∀ a b, R a b → R b a) (xs ys : List (Fin n)) :
    ys.length = xs.length + 1 → xs.Nodup → ys.Nodup →
      (∀ z ∈ xs, z ∉ ys) → (∀ x ∈ xs, ∀ y ∈ ys, R x y) →
      ∃ p : VertPath (Fin n), p.toList.IsChain R ∧
        (∀ z ∈ p.toList, z ∈ xs ∨ z ∈ ys) ∧
        (∀ z ∈ p.toList.head?, z ∈ ys) ∧ ∀ x ∈ xs, x ∈ p.toList := by
  induction xs generalizing ys with
  | nil =>
    intro hlen hxs hys hdisj hedge
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      cases ys with
      | nil =>
        refine ⟨⟨[y], List.cons_ne_nil _ _, List.nodup_singleton y⟩,
          List.isChain_singleton y, ?_, ?_, ?_⟩
        · intro z hz
          rw [List.mem_singleton] at hz
          subst hz
          exact Or.inr List.mem_cons_self
        · intro z hz
          rw [List.head?_singleton, Option.mem_some] at hz
          subst hz
          exact List.mem_cons_self
        · intro z hz
          exact (List.not_mem_nil hz).elim
      | cons z zs => simp at hlen
  | cons x xs ih =>
    intro hlen hxs hys hdisj hedge
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rw [List.nodup_cons] at hxs hys
      obtain ⟨hx, hxs'⟩ := hxs
      obtain ⟨hy, hys'⟩ := hys
      have hlen' : ys.length = xs.length + 1 := by
        simp only [List.length_cons] at hlen
        omega
      have hdisj' : ∀ z ∈ xs, z ∉ ys := fun z hz hzy ↦
        hdisj z (List.mem_cons_of_mem x hz) (List.mem_cons_of_mem y hzy)
      have hedge' : ∀ x' ∈ xs, ∀ y' ∈ ys, R x' y' := fun x' hx' y' hy' ↦
        hedge x' (List.mem_cons_of_mem x hx') y' (List.mem_cons_of_mem y hy')
      obtain ⟨p', hchain', hmem', hhead', hcov'⟩ :=
        ih ys hlen' hxs' hys' hdisj' hedge'
      refine ⟨⟨y :: x :: p'.toList, List.cons_ne_nil _ _, ?_⟩, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨?_, ?_⟩
        · intro hmem
          rw [List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · exact (hdisj x List.mem_cons_self)
              (List.mem_cons.mpr (Or.inl heq.symm))
          · rcases hmem' _ hmem with hz | hz
            · exact (hdisj y (List.mem_cons_of_mem x hz)) List.mem_cons_self
            · exact hy hz
        · rw [List.nodup_cons]
          refine ⟨?_, p'.nodup⟩
          intro hmem
          rcases hmem' _ hmem with hz | hz
          · exact hx hz
          · exact (hdisj x List.mem_cons_self) (List.mem_cons_of_mem y hz)
      · refine List.isChain_cons.mpr ⟨?_, List.isChain_cons.mpr ⟨?_, hchain'⟩⟩
        · intro z hz
          rw [List.head?_cons, Option.mem_some] at hz
          subst hz
          exact hR _ _ (hedge x List.mem_cons_self y List.mem_cons_self)
        · intro z hz
          exact hedge x List.mem_cons_self z
            (List.mem_cons_of_mem y (hhead' z hz))
      · intro z hz
        rw [List.mem_cons, List.mem_cons] at hz
        rcases hz with rfl | rfl | hz
        · exact Or.inr List.mem_cons_self
        · exact Or.inl List.mem_cons_self
        · rcases hmem' _ hz with h | h
          · exact Or.inl (List.mem_cons_of_mem x h)
          · exact Or.inr (List.mem_cons_of_mem y h)
      · intro z hz
        rw [List.head?_cons, Option.mem_some] at hz
        subst hz
        exact List.mem_cons_self
      · intro z hz
        rw [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact List.mem_cons_of_mem y List.mem_cons_self
        · exact List.mem_cons_of_mem y (List.mem_cons_of_mem x (hcov' z hz))

/-- Finset version of `alt_path_list`: any `S` with `|S| + 1 ≤ |Y₀|` and
all `S`–`Y₀` pairs `R`-related is covered by a single `R`-chain. -/
private theorem alt_path_exists {n : ℕ} {R : Fin n → Fin n → Prop}
    (hR : ∀ a b, R a b → R b a)
    {S Y₀ : Finset (Fin n)} (hdisj : Disjoint S Y₀)
    (hedge : ∀ x ∈ S, ∀ y ∈ Y₀, R x y)
    (hcard : S.card + 1 ≤ Y₀.card) :
    ∃ p : VertPath (Fin n), p.toList.IsChain R ∧ ∀ x ∈ S, x ∈ p.toList := by
  classical
  obtain ⟨p, hchain, _, _, hcov⟩ := alt_path_list hR S.toList
    (Y₀.toList.take (S.card + 1))
    (by rw [List.length_take, Finset.length_toList, Finset.length_toList,
        min_eq_left hcard])
    (Finset.nodup_toList _)
    ((Finset.nodup_toList _).sublist (List.take_sublist _ _))
    (fun z hz hzy ↦
      (Finset.disjoint_left.mp hdisj (Finset.mem_toList.mp hz))
        (Finset.mem_toList.mp (List.Sublist.mem hzy (List.take_sublist _ _))))
    (fun x hx y hy ↦
      hedge x (Finset.mem_toList.mp hx) y
        (Finset.mem_toList.mp (List.Sublist.mem hy (List.take_sublist _ _))))
  exact ⟨p, hchain, fun x hx ↦ hcov x (Finset.mem_toList.mpr hx)⟩

/-- Grouped alternating cover: if every `x ∈ X'` is `R`-related to every
`y ∈ Y₀`, and `|X'| ≤ k · (|Y₀| - 1)`, then `X'` is covered by at most `k`
`R`-chains.  Used for the ≤ 21 extra paths of Proposition 3.4. -/
private theorem alt_cover {n : ℕ} {R : Fin n → Fin n → Prop}
    (hR : ∀ a b, R a b → R b a) (Y₀ : Finset (Fin n))
    (X' : Finset (Fin n)) (k : ℕ) (hdisj : Disjoint X' Y₀)
    (hedge : ∀ x ∈ X', ∀ y ∈ Y₀, R x y)
    (hcard : X'.card ≤ k * (Y₀.card - 1)) :
    ∃ F : Finset (VertPath (Fin n)), (∀ p ∈ F, p.toList.IsChain R) ∧
      (∀ x ∈ X', ∃ p ∈ F, x ∈ p.toList) ∧ F.card ≤ k := by
  classical
  revert k hdisj hedge hcard
  refine Finset.strongInductionOn X' (p := fun T ↦ ∀ k : ℕ, Disjoint T Y₀ →
      (∀ x ∈ T, ∀ y ∈ Y₀, R x y) → T.card ≤ k * (Y₀.card - 1) →
      ∃ F : Finset (VertPath (Fin n)), (∀ p ∈ F, p.toList.IsChain R) ∧
        (∀ x ∈ T, ∃ p ∈ F, x ∈ p.toList) ∧ F.card ≤ k)
    fun T ihT k hdisjT hedgeT hcardT ↦ ?_
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · exact ⟨∅, fun p hp ↦ by simp at hp, fun x hx ↦ by simp at hx, by simp⟩
  · have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [Nat.zero_mul] at hcardT
        have h2 := Finset.card_pos.mpr hTne
        omega
      · exact hk
    have hY0 : 2 ≤ Y₀.card := by
      by_contra hlt
      push_neg at hlt
      have hz : Y₀.card - 1 = 0 := by omega
      rw [hz, Nat.mul_zero] at hcardT
      have h2 := Finset.card_pos.mpr hTne
      omega
    by_cases hsmall : T.card ≤ Y₀.card - 1
    · obtain ⟨p, hpchain, hpcov⟩ := alt_path_exists hR hdisjT hedgeT (by omega)
      exact ⟨{p},
        fun q hq ↦ by rw [Finset.mem_singleton] at hq; rwa [hq],
        fun x hx ↦ ⟨p, Finset.mem_singleton_self _, hpcov x hx⟩,
        by rw [Finset.card_singleton]; exact hk1⟩
    · push_neg at hsmall
      obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq (le_of_lt hsmall)
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨p, hpchain, hpcov⟩ := alt_path_exists hR
        (Finset.disjoint_left.mpr fun x hx hy ↦
          Finset.disjoint_left.mp hdisjT (hST hx) hy)
        (fun x hx y hy ↦ hedgeT x (hST hx) y hy) (by omega)
      have hcard' : (T \ S).card ≤ (k - 1) * (Y₀.card - 1) := by
        rw [Finset.card_sdiff_of_subset hST]
        have hmul : (k - 1) * (Y₀.card - 1) =
            k * (Y₀.card - 1) - (Y₀.card - 1) := by
          rw [Nat.sub_mul, Nat.one_mul]
        omega
      obtain ⟨F', hF'chain, hF'cov, hF'card⟩ := ihT (T \ S)
        (Finset.sdiff_ssubset hST hSne) (k - 1)
        (Finset.disjoint_left.mpr fun x hx hy ↦
          Finset.disjoint_left.mp hdisjT (Finset.mem_sdiff.mp hx).1 hy)
        (fun x hx y hy ↦ hedgeT x (Finset.mem_sdiff.mp hx).1 y hy)
        hcard'
      refine ⟨insert p F', ?_, ?_, ?_⟩
      · intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact hpchain
        · exact hF'chain q hq
      · intro x hx
        by_cases hxS : x ∈ S
        · exact ⟨p, Finset.mem_insert_self _ _, hpcov x hxS⟩
        · obtain ⟨q, hq, hqx⟩ := hF'cov x (Finset.mem_sdiff.mpr ⟨hx, hxS⟩)
          exact ⟨q, Finset.mem_insert_of_mem hq, hqx⟩
      · calc (insert p F').card ≤ F'.card + 1 := Finset.card_insert_le p F'
          _ ≤ k := by omega

/-- Pushing a `HasCoverLt` through a bijection. -/
private theorem HasCoverLt.comap {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph W} {f : V → W}
    (hf : Function.Injective f) (hfs : Function.Surjective f) {b : ℝ}
    (h : HasCoverLt (G.comap f) b) : HasCoverLt G b := by
  classical
  obtain ⟨c, P, ⟨hmono, hcover⟩, hcard⟩ := h
  have hinj : Function.Injective fun p : VertPath V ↦ p.map f hf :=
    fun p q hpq ↦
      VertPath.ext (List.map_injective_iff.mpr hf (congrArg VertPath.toList hpq))
  refine ⟨c, P.map ⟨fun p ↦ p.map f hf, hinj⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
    exact (hmono p hp).map hf
  · intro w
    obtain ⟨v, rfl⟩ := hfs w
    obtain ⟨p, hp, hvp⟩ := hcover v
    exact ⟨p.map f hf, Finset.mem_map.mpr ⟨p, hp, rfl⟩,
      VertPath.mem_map.mpr ⟨v, hvp, rfl⟩⟩
  · rw [Finset.card_map]
    exact hcard

set_option maxHeartbeats 1000000 in
/-- Inductive step of Proposition 3.4: for `n > 20⁴`, if the bound
`√m + 20⁴` holds for all `m < n`, then every graph on `n` vertices has a
same-color cover of size `< √n + 20⁴`.

Following the paper: apply `long_path_structure` to get a long
monochromatic path `P` such that every `y ∉ P` has at most `4√n`
`γ`-neighbors on `P`.  If the `Y₀`-set (no `γ`-neighbor on `P`) or `Y`
itself is small, `tail_pairing_bound` finishes.  Otherwise use
`few_paths_of_min_degree` to cover `Y` and almost all of `P` by fewer than
`√n` paths of the other color; the uncovered subset `X'` of `P` has at
most `21 (|Y₀| - 1)` vertices, so it is covered by ≤ 21 alternating
paths of the other color through `Y₀`. -/
private theorem weak_sqrt_step {n : ℕ}
    (hind : ∀ m < n, AllCoverLt m (Real.sqrt m + (20 : ℝ) ^ 4))
    (hn : (20 : ℝ) ^ 4 < (n : ℝ))
    (G : SimpleGraph (Fin n)) :
    HasCoverLt G (Real.sqrt n + (20 : ℝ) ^ 4) := by
  classical
  set C : ℝ := 20 ^ 4 with hCdef
  have hnR : (0 : ℝ) < n := by
    have : (0 : ℝ) < (20 : ℝ) ^ 4 := by norm_num
    linarith
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hsqrt : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hn4pos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos hnR _
  have hn4sq : ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt n := by
    have h2 : ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 =
        ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ ((2 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    rw [h2, ← Real.rpow_mul hnR.le, Real.sqrt_eq_rpow]
    have e : (1 : ℝ) / 4 * ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
    rw [e]
  have hn4gt : (20 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have h204 : (20 : ℝ) = ((20 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 20),
        show ((4:ℕ):ℝ) * (1/4) = 1 by norm_num, Real.rpow_one]
    rw [h204]
    exact Real.rpow_lt_rpow (by norm_num) hn (by norm_num)
  have h20n4 : 20 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.sqrt n := by
    have h := mul_lt_mul_of_pos_right hn4gt hn4pos
    rw [← pow_two, hn4sq] at h
    exact h.le
  have hsqrt400 : (400 : ℝ) < Real.sqrt n := by
    have e : ((400 : ℝ) ^ 2) < n := by
      have h2 : (20:ℝ)^4 = 400^2 := by norm_num
      linarith
    calc (400 : ℝ) = Real.sqrt ((400:ℝ)^2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt n := Real.sqrt_lt_sqrt (by positivity) e
  have hbig : 12 * Real.sqrt n + 2 < n := by
    calc 12 * Real.sqrt n + 2 < 400 * Real.sqrt n := by linarith
      _ < Real.sqrt n * Real.sqrt n := mul_lt_mul_of_pos_right hsqrt400 hsqrt
      _ = n := Real.mul_self_sqrt hnR.le
  by_cases hG : HasCoverLe G (Real.sqrt n + (C - 1))
  · obtain ⟨c, F, hF, hcard⟩ := hG
    exact ⟨c, F, hF, lt_of_le_of_lt hcard (by linarith)⟩
  obtain ⟨γ, P, hPmono, hPleft, hNbrs⟩ := long_path_structure
    (C₁ := C) (C₂ := C - 1) (by linarith)
    (by
      have e : C - (C - 1) + 1 = 2 := by ring
      rw [e]
      calc (10:ℝ)^4 * 2^4 = 20^4 := by norm_num
        _ = C := hCdef.symm
        _ < n := hn)
    hind G hG
  have hΔ : C - (C - 1) + 1 = 2 := by ring
  rw [hΔ] at hPleft hNbrs
  set X := P.toList.toFinset with hXdef
  set Y := Xᶜ with hYdef
  set Y₀ := Y.filter (fun y ↦ ∀ x ∈ P.toList, ¬ Color.adj G γ x y) with hY0def
  have hXcard : X.card = P.toList.length := List.toFinset_card_of_nodup P.nodup
  have hXlen : X.card ≤ n := by
    rw [hXcard]
    exact le_trans P.nodup.length_le_card (le_of_eq (Fintype.card_fin n))
  have hXlenR : (X.card : ℝ) ≤ n := by exact_mod_cast hXlen
  have hYcard : Y.card = n - X.card := by
    rw [hYdef, Finset.card_compl, Fintype.card_fin]
  have hdisjXY : Disjoint X Y :=
    Finset.disjoint_left.mpr fun a ha hb ↦ (Finset.mem_compl.mp hb) ha
  have hY0sub : Y₀ ⊆ Y := Finset.filter_subset _ _
  have hYiff : ∀ y, y ∈ Y ↔ y ∉ P.toList := fun y ↦ by
    rw [hYdef, Finset.mem_compl, hXdef, List.mem_toFinset]
  have hY0iff : ∀ y, y ∈ Y₀ ↔
      y ∉ P.toList ∧ ∀ x ∈ P.toList, ¬ Color.adj G γ x y := by
    intro y
    rw [hY0def, Finset.mem_filter, hYiff y]
  have hYle : (Y.card : ℝ) ≤ Real.sqrt n + 20 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have hle : ((n - X.card : ℕ) : ℝ) ≤
        Real.sqrt n + 20 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Nat.cast_sub hXlen, hXcard]
      linarith [hPleft]
    rw [hYcard]
    exact hle
  have hYle2 : (Y.card : ℝ) ≤ 2 * Real.sqrt n := by linarith
  have hYleA : (Y.card : ℝ) ≤ 3 * Real.sqrt n / 2 + (2 * C - 4) := by
    have h20half : 20 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤
        Real.sqrt n / 2 + (2 * C - 4) := by
      by_cases h40 : (40 : ℝ) ^ 4 ≤ n
      · have h404 : (40 : ℝ) = ((40 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 40),
            show ((4:ℕ):ℝ) * (1/4) = 1 by norm_num, Real.rpow_one]
        have h40n4 : (40 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
          rw [h404]
          exact Real.rpow_le_rpow (by norm_num) h40 (by norm_num)
        have hC4 : (0:ℝ) ≤ 2 * C - 4 := by rw [hCdef]; norm_num
        nlinarith [hn4sq, mul_nonneg (sub_nonneg.mpr h40n4) hn4pos.le, hC4]
      · push_neg at h40
        have h404 : (40 : ℝ) = ((40 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 40),
            show ((4:ℕ):ℝ) * (1/4) = 1 by norm_num, Real.rpow_one]
        have h40n4 : (n : ℝ) ^ ((1 : ℝ) / 4) < 40 := by
          rw [h404]
          exact Real.rpow_lt_rpow (by positivity) h40 (by norm_num)
        have hCv : C = 160000 := by rw [hCdef]; norm_num
        linarith [h40n4, hCv, hsqrt.le]
    linarith
  by_cases hcase : (Y₀.card : ℝ) ≤ Real.sqrt n / 2 ∨
      (Y.card : ℝ) ≤ Real.sqrt n
  · obtain ⟨c, F, ⟨hmono, hcov⟩, hcard⟩ :=
      tail_pairing_bound_color G P hPmono Y Y₀ hYiff hY0iff
    refine ⟨c, F, ⟨hmono, hcov⟩, ?_⟩
    have hC2 : (2 : ℝ) ≤ C := by rw [hCdef]; norm_num
    have hbound : (2 : ℝ) + (Y.card : ℝ) / 2 + (Y₀.card : ℝ) / 2 ≤
        Real.sqrt n + C := by
      rcases hcase with hY0 | hY
      · linarith
      · have hY0b : (Y₀.card : ℝ) ≤ Real.sqrt n := by
          have hsub := Finset.card_le_card hY0sub
          have hle : (Y₀.card : ℝ) ≤ Y.card := by exact_mod_cast hsub
          linarith
        linarith
    exact lt_of_lt_of_le hcard hbound
  · push_neg at hcase
    obtain ⟨hY0gt, hYgt⟩ := hcase
    set m := ⌈4 * Real.sqrt (n : ℝ)⌉₊ with hmdef
    set H := adjXYGraph G hdisjXY γ.other with hHdef
    have hmR : (m : ℝ) < 4 * Real.sqrt n + 1 := by
      rw [hmdef]
      exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hsqrt.le)
    have hYpos' : 0 < Y.card := by
      have h : (0:ℝ) < Y.card := lt_trans hsqrt hYgt
      exact_mod_cast h
    have hYposR : (0:ℝ) < (Y.card : ℝ) := by exact_mod_cast hYpos'
    have hdegN : ∀ y ∈ Y, X.card - m ≤
        (X.filter fun x ↦ Color.adj G γ.other x y).card := by
      intro y hy
      have hyP : y ∉ P.toList := (hYiff y).mp hy
      have hB := hNbrs y hyP
      set B := X.filter (fun x ↦ Color.adj G γ x y) with hBdef
      have hBset : {x : Fin n | x ∈ P.toList ∧ Color.adj G γ x y} =
          (B : Set (Fin n)) := by
        ext x
        simp [hBdef, hXdef, Finset.coe_filter, List.mem_toFinset]
      rw [hBset, Set.ncard_coe_finset] at hB
      have hBm : B.card ≤ m := by
        rw [hmdef]
        have h' := Nat.ceil_le_ceil
          (show (B.card : ℝ) ≤ 4 * Real.sqrt n by linarith)
        rwa [Nat.ceil_natCast] at h'
      have hunion : B ∪ (X.filter fun x ↦ Color.adj G γ.other x y) = X := by
        ext x
        simp only [hBdef, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hxX, -⟩ | ⟨hxX, -⟩) <;> exact hxX
        · intro hxX
          have hxy : x ≠ y := fun e ↦ by
            subst e
            exact (Finset.mem_compl.mp hy) hxX
          rcases Color.adj_or_adj_other G hxy with h | h
          · exact Or.inl ⟨hxX, h⟩
          · exact Or.inr ⟨hxX, h⟩
      have hsplit : X.card ≤ B.card +
          (X.filter fun x ↦ Color.adj G γ.other x y).card := by
        have hc : X.card =
            (B ∪ (X.filter fun x ↦ Color.adj G γ.other x y)).card :=
          congrArg Finset.card hunion.symm
        rw [hc]
        exact Finset.card_union_le B _
      omega
    have hcardXY : Y.card + 2 * m ≤ X.card := by
      have hXY : (X.card : ℝ) + Y.card = n := by
        have hcast : ((n - X.card : ℕ) : ℝ) = (n : ℝ) - X.card :=
          Nat.cast_sub hXlen
        have hYc : (Y.card : ℝ) = (n : ℝ) - X.card := by
          rw [hYcard]
          exact hcast
        linarith
      have hR : (Y.card : ℝ) + 2 * m < (X.card : ℝ) := by linarith
      exact_mod_cast hR.le
    have hbip : BipartiteOn H X Y :=
      ⟨hdisjXY, fun a b h ↦ bip_ramsey_path.Color.adjXY.across
        (show Color.adjXY G X Y γ.other a b from h)⟩
    have hdeg : ∀ y ∈ Y, (H.neighborFinset y).card ≥ X.card - m := by
      intro y hy
      have hsub : (X.filter fun x ↦ Color.adj G γ.other x y) ⊆
          H.neighborFinset y := by
        intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hxX, hadj⟩ := hx
        rw [SimpleGraph.mem_neighborFinset]
        show Color.adjXY G X Y γ.other y x
        exact adjXY_of_across_adj G (Or.inr ⟨hy, hxX⟩) (Color.adj_symm G hadj)
      calc X.card - m ≤ (X.filter fun x ↦ Color.adj G γ.other x y).card :=
            hdegN y hy
        _ ≤ (H.neighborFinset y).card := Finset.card_le_card hsub
    obtain ⟨P_fam, hPf_chain, hPf_mem, hPf_cov, hPf_card, hPf_uncov⟩ :=
      few_paths_of_min_degree H X Y m hbip hYpos' hcardXY hdeg
    have hPfmono : ∀ p ∈ P_fam, p.IsMonochromatic G γ.other := fun p hp ↦
      (hPf_chain p hp).imp fun _ _ h ↦ adjXY_to_adj G hdisjXY h
    set T := P_fam.biUnion VertPath.verts with hTdef
    set X' := X \ T with hX'def
    have hX'card : (X'.card : ℝ) ≤ 10 * Real.sqrt n + 2 := by
      have h1 : (X'.card : ℝ) ≤ (Y.card : ℝ) + 2 * m := by
        have hle : X'.card ≤ Y.card + 2 * m := by
          rw [hX'def, hTdef]
          exact hPf_uncov
        exact_mod_cast hle
      linarith
    have hdisjX' : Disjoint X' Y₀ :=
      Finset.disjoint_left.mpr fun x hx hy ↦
        Finset.disjoint_left.mp hdisjXY (Finset.mem_sdiff.mp hx).1 (hY0sub hy)
    have hedge : ∀ x ∈ X', ∀ y ∈ Y₀, Color.adj G γ.other x y := by
      intro x hx y hy
      have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
      have hxP : x ∈ P.toList := by
        rw [hXdef] at hxX
        exact List.mem_toFinset.mp hxX
      have hyP : y ∉ P.toList := (hYiff y).mp (hY0sub hy)
      have hxy : x ≠ y := fun e ↦ by
        subst e
        exact hyP hxP
      have hnadj : ¬ Color.adj G γ x y := by
        have h : y ∈ Y₀ := hy
        rw [hY0iff y] at h
        exact h.2 x hxP
      exact (Color.adj_iff_not_adj_other G (c := γ.other) hxy).mpr
        (show ¬ Color.adj G γ.other.other x y by
          rw [Color.other_other]
          exact hnadj)
    have hcardX' : X'.card ≤ 21 * (Y₀.card - 1) := by
      have hY0ge1 : 1 ≤ Y₀.card := by
        have h : (0:ℝ) < Y₀.card := by linarith
        exact_mod_cast h
      have hR : (X'.card : ℝ) ≤ ((21 * (Y₀.card - 1) : ℕ) : ℝ) := by
        have hcast : ((21 * (Y₀.card - 1) : ℕ) : ℝ) =
            21 * ((Y₀.card : ℝ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub hY0ge1, Nat.cast_one]
          norm_num
        rw [hcast]
        linarith
      exact_mod_cast hR
    obtain ⟨F₂, hF₂chain, hF₂cov, hF₂card⟩ := alt_cover
      (fun _ _ h ↦ Color.adj_symm G h) Y₀ X' 21 hdisjX' hedge hcardX'
    refine ⟨γ.other, P_fam ∪ F₂, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · intro p hp
      rw [Finset.mem_union] at hp
      rcases hp with hp | hp
      · exact hPfmono p hp
      · exact hF₂chain p hp
    · intro v
      by_cases hvY : v ∈ Y
      · obtain ⟨p, hp, hvp⟩ := hPf_cov v hvY
        exact ⟨p, Finset.mem_union_left _ hp, hvp⟩
      · have hvX : v ∈ X := by
          by_contra h
          exact hvY (Finset.mem_compl.mpr h)
        by_cases hvT : v ∈ T
        · rw [hTdef, Finset.mem_biUnion] at hvT
          obtain ⟨p, hp, hvp⟩ := hvT
          exact ⟨p, Finset.mem_union_left _ hp, VertPath.mem_verts.mp hvp⟩
        · obtain ⟨p, hp, hvp⟩ := hF₂cov v (Finset.mem_sdiff.mpr ⟨hvX, hvT⟩)
          exact ⟨p, Finset.mem_union_right _ hp, hvp⟩
    · have hF1 : (P_fam.card : ℝ) < Real.sqrt n := by
        calc (P_fam.card : ℝ) ≤ ((X.card / Y.card : ℕ) : ℝ) := by
              exact_mod_cast hPf_card
          _ ≤ (X.card : ℝ) / Y.card := Nat.cast_div_le
          _ ≤ (n : ℝ) / Y.card :=
              div_le_div_of_nonneg_right hXlenR hYposR.le
          _ < (n : ℝ) / Real.sqrt n :=
              div_lt_div_of_pos_left hnR hsqrt hYgt
          _ = Real.sqrt n := by
              rw [div_eq_iff hsqrt.ne']
              exact (Real.mul_self_sqrt hnR.le).symm
      have hF2 : (F₂.card : ℝ) ≤ 21 := by exact_mod_cast hF₂card
      have h1 : ((P_fam ∪ F₂).card : ℝ) ≤ (P_fam.card : ℝ) + F₂.card := by
        exact_mod_cast Finset.card_union_le P_fam F₂
      have hC21 : (21:ℝ) < C := by rw [hCdef]; norm_num
      linarith

/-- **PVW24 Proposition 3.4 (weak bound).**  For all `n`,
`f(n) < √n + 20⁴`. -/
theorem weak_sqrt_bound (n : ℕ) :
    AllCoverLt n (Real.sqrt n + 20 ^ 4) := by
  classical
  refine Nat.strong_induction_on n fun n ih ↦ ?_
  intro W instF instD hW G
  by_cases hbase : n ≤ 20 ^ 4
  · refine HasCoverLt.self G ?_
    rw [hW]
    by_cases hn0 : n = 0
    · subst hn0
      simp only [Nat.cast_zero, Real.sqrt_zero, zero_add]
      norm_num
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnR : (0:ℝ) < n := by exact_mod_cast hn1
      have hsqrt : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
      have hle : (n:ℝ) ≤ 20^4 := by exact_mod_cast hbase
      linarith
  · have hnlt : 20 ^ 4 < n := Nat.lt_of_not_ge hbase
    have hnR : (20 : ℝ) ^ 4 < (n : ℝ) := by
      have h : ((20 ^ 4 : ℕ) : ℝ) < n := by exact_mod_cast hnlt
      norm_num at h ⊢
      exact h
    have e : W ≃ Fin n := Fintype.equivFinOfCardEq hW
    exact HasCoverLt.comap e.symm.injective e.symm.surjective
      (weak_sqrt_step ih hnR (G.comap e.symm))

/-- Transport of `HasCoverLe` through the complement graph (colour swap). -/
private theorem HasCoverLe.of_compl {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {b : ℝ} (h : HasCoverLe Gᶜ b) : HasCoverLe G b := by
  obtain ⟨c, F, ⟨hmono, hcov⟩, hcard⟩ := h
  cases c with
  | red =>
    exact ⟨.blue, F, ⟨fun p hp ↦ (hmono p hp).imp fun _ _ hab ↦
      (compl_red_iff G).mp hab, hcov⟩, hcard⟩
  | blue =>
    exact ⟨.red, F, ⟨fun p hp ↦ (hmono p hp).imp fun _ _ hab ↦
      (compl_blue_iff G).mp hab, hcov⟩, hcard⟩

/-- Membership in `fullNbr`. -/
private theorem mem_fullNbr {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {X Y : Finset V} {x : V} :
    x ∈ fullNbr G X Y ↔ x ∈ X ∧ (G.neighborFinset x).card = Y.card :=
  Finset.mem_filter

/-- Sharp form of Lemma 3.3 for a blue path: the cover built in
`tail_pairing_bound` has size at most `1 + ⌈|Y ∖ Y₀|/2⌉ + |Y₀|`. -/
private theorem tail_pairing_sharp_aux {n : ℕ} (G : SimpleGraph (Fin n))
    (P : VertPath (Fin n)) (hP : P.IsMonochromatic G .blue)
    (Y Y₀ : Finset (Fin n))
    (hY : ∀ y, y ∈ Y ↔ y ∉ P.toList)
    (hY0 : ∀ y, y ∈ Y₀ ↔ y ∉ P.toList ∧
      ∀ x ∈ P.toList, ¬ Color.adj G .blue x y) :
    HasCoverLe G (1 + (((Y \ Y₀).card + 1) / 2 : ℕ) + Y₀.card) := by
  classical
  have hY0sub : Y₀ ⊆ Y := fun y hy => (hY y).mpr ((hY0 y).mp hy).1
  have hS : ∀ y ∈ Y \ Y₀, y ∉ P.toList ∧
      ∃ x ∈ P.toList, Color.adj G .blue x y := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    have hyP : y ∉ P.toList := (hY y).mp hy.1
    refine ⟨hyP, ?_⟩
    by_contra hcon
    push_neg at hcon
    exact hy.2 ((hY0 y).mpr ⟨hyP, hcon⟩)
  obtain ⟨F, hFmono, hFcov, hFcard⟩ := pair_family G P hP (Y \ Y₀) hS
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
  · have hc : (insert P (F ∪ Y₀.map VertPath.singletonEmbedding)).card ≤
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
    have h2 : ((insert P (F ∪ Y₀.map VertPath.singletonEmbedding)).card : ℝ) ≤
        ((((Y \ Y₀).card + 1) / 2 : ℕ) : ℝ) + 1 + Y₀.card := by
      have h3 : ((insert P (F ∪ Y₀.map VertPath.singletonEmbedding)).card : ℝ) ≤
          ((((Y \ Y₀).card + 1) / 2 + 1 + Y₀.card : ℕ) : ℝ) := by
        exact_mod_cast hc
      rwa [Nat.cast_add, Nat.cast_add, Nat.cast_one] at h3
    linarith

/-- `tail_pairing_sharp_aux` for a monochromatic path of either colour. -/
private theorem tail_pairing_sharp {n : ℕ} (G : SimpleGraph (Fin n))
    (P : VertPath (Fin n)) {γ : Color} (hP : P.IsMonochromatic G γ)
    (Y Y₀ : Finset (Fin n))
    (hY : ∀ y, y ∈ Y ↔ y ∉ P.toList)
    (hY0 : ∀ y, y ∈ Y₀ ↔ y ∉ P.toList ∧
      ∀ x ∈ P.toList, ¬ Color.adj G γ x y) :
    HasCoverLe G (1 + (((Y \ Y₀).card + 1) / 2 : ℕ) + Y₀.card) := by
  cases γ with
  | blue => exact tail_pairing_sharp_aux G P hP Y Y₀ hY hY0
  | red =>
    have hP' : P.IsMonochromatic Gᶜ .blue :=
      hP.imp fun _ _ h ↦ (compl_blue_iff G).mpr h
    have hY0' : ∀ y, y ∈ Y₀ ↔
        y ∉ P.toList ∧ ∀ x ∈ P.toList, ¬ Color.adj Gᶜ .blue x y := by
      intro y
      rw [hY0 y]
      exact Iff.and Iff.rfl (forall_congr' fun x ↦ forall_congr' fun _ ↦
        not_congr (compl_blue_iff G).symm)
    exact HasCoverLe.of_compl G
      (tail_pairing_sharp_aux Gᶜ P hP' Y Y₀ hY hY0')

set_option maxHeartbeats 1000000 in
/-- **PVW24 Theorem 1.3 — the Erdős–Gyárfás conjecture.**  For all
`n > 20^{40}`, every 2-edge-coloured `K_n` has a vertex cover by at most `√n`
monochromatic paths, all of the same colour. -/
theorem monochromatic_path_cover {n : ℕ} (hn : 20 ^ 40 < n)
    (G : SimpleGraph (Fin n)) :
    ∃ c : Color, ∃ P : Finset (VertPath (Fin n)),
      IsSameColorCover G c P ∧ (P.card : ℝ) ≤ Real.sqrt n := by
  classical
  show HasCoverLe G (Real.sqrt n)
  by_cases hG : HasCoverLe G (Real.sqrt n)
  · exact hG
  -- Constants: `C = 20⁴`, `a = n^{1/4}`, `α = 11C/a`.
  set C : ℝ := 20 ^ 4 with hCdef
  have hCpos : (0 : ℝ) < C := by rw [hCdef]; norm_num
  have hnR40 : (20 : ℝ) ^ 40 < (n : ℝ) := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by linarith [hnR40]
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hsqrt : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  -- Induction hypothesis from the weak bound (Proposition 3.4).
  have hind : ∀ m < n, AllCoverLt m (Real.sqrt m + C) := by
    intro m _
    rw [hCdef]
    exact weak_sqrt_bound m
  -- Lemma 3.2 with `C₁ = C`, `C₂ = 0`, so `Δ = C + 1`.
  have hncond : (10 : ℝ) ^ 4 * (C - 0 + 1) ^ 4 < (n : ℝ) := by
    have h1 : (10 : ℝ) ^ 4 * (C - 0 + 1) ^ 4 ≤ (20 : ℝ) ^ 40 := by
      rw [hCdef]; norm_num
    exact lt_of_le_of_lt h1 hnR40
  obtain ⟨γ, P, hPmono, hPleft, hNbrs⟩ :=
    long_path_structure (C₁ := C) (C₂ := 0) hCpos.le hncond hind G
      (by simpa using hG)
  simp only [sub_zero] at hPleft hNbrs
  set a : ℝ := (n : ℝ) ^ ((1 : ℝ) / 4) with hadef
  have hapos : (0 : ℝ) < a := Real.rpow_pos_of_pos hnR _
  have hane : a ≠ 0 := hapos.ne'
  have ha2 : a ^ 2 = Real.sqrt n := by
    have h2 : a ^ 2 = a ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ 2).symm
    rw [h2, hadef, ← Real.rpow_mul hnR.le,
      show (1 : ℝ) / 4 * ((2 : ℕ) : ℝ) = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  have ha4 : a ^ 4 = (n : ℝ) := by
    have e : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [e, ha2, Real.sq_sqrt hnR.le]
  have h2040 : ((20 : ℝ) ^ 40) ^ ((1 : ℝ) / 4) = (20 : ℝ) ^ 10 := by
    have e1 : (20 : ℝ) ^ 40 = (20 : ℝ) ^ ((40 : ℕ) : ℝ) :=
      (Real.rpow_natCast 20 40).symm
    rw [e1, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 20),
      show ((40 : ℕ) : ℝ) * (1 / 4) = ((10 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have ha20 : (20 : ℝ) ^ 10 < a := by
    rw [← h2040, hadef]
    exact Real.rpow_lt_rpow (by norm_num) hnR40 (by norm_num)
  have ha1 : (1 : ℝ) ≤ a := by nlinarith [ha20]
  have ha2big : (5 : ℝ) ≤ a ^ 2 := by
    have h1 : (20 : ℝ) ^ 10 * a < a * a := mul_lt_mul_of_pos_right ha20 hapos
    nlinarith [h1, ha20]
  set α : ℝ := 11 * C / a with hαdef
  have hαpos : (0 : ℝ) < α := div_pos (mul_pos (by norm_num) hCpos) hapos
  have hαlt : α < 1 / 4 := by
    rw [hαdef, hCdef, div_lt_iff₀ hapos]
    nlinarith [ha20]
  have hαsq : α * Real.sqrt n = 11 * C * a := by
    rw [← ha2, hαdef]
    field_simp
  -- `X` = vertex set of `P`, `Y` = complement, `Y₀` = no `γ`-edge to `P`.
  set X := P.toList.toFinset with hXdef
  set Y := Xᶜ with hYdef
  set Y₀ := Y.filter (fun y ↦ ∀ x ∈ P.toList, ¬ Color.adj G γ x y) with hY0def
  have hXcard : X.card = P.toList.length := List.toFinset_card_of_nodup P.nodup
  have hXlen : X.card ≤ n := by
    rw [hXcard]
    exact le_trans P.nodup.length_le_card (le_of_eq (Fintype.card_fin n))
  have hYcard : Y.card = n - X.card := by
    rw [hYdef, Finset.card_compl, Fintype.card_fin]
  have hYcardR : (Y.card : ℝ) = (n : ℝ) - X.card := by
    rw [hYcard, Nat.cast_sub hXlen]
  have hXcardR : (X.card : ℝ) = (n : ℝ) - Y.card := by linarith [hYcardR]
  have hdisjXY : Disjoint X Y :=
    Finset.disjoint_left.mpr fun a ha hb ↦ (Finset.mem_compl.mp hb) ha
  have hY0sub : Y₀ ⊆ Y := Finset.filter_subset _ _
  have hYiff : ∀ y, y ∈ Y ↔ y ∉ P.toList := fun y ↦ by
    rw [hYdef, Finset.mem_compl, hXdef, List.mem_toFinset]
  have hY0iff : ∀ y, y ∈ Y₀ ↔
      y ∉ P.toList ∧ ∀ x ∈ P.toList, ¬ Color.adj G γ x y := by
    intro y
    rw [hY0def, Finset.mem_filter, hYiff y]
  -- `|Y| ≤ (1 + α) √n`.
  have hYle : (Y.card : ℝ) ≤ Real.sqrt n + 10 * (C + 1) * a := by
    have hle : ((n - X.card : ℕ) : ℝ) ≤ Real.sqrt n + 10 * (C + 1) * a := by
      rw [Nat.cast_sub hXlen, hXcard]
      exact hPleft
    rw [hYcard]
    exact hle
  have h10 : 10 * (C + 1) ≤ 11 * C := by rw [hCdef]; norm_num
  have hYbound : (Y.card : ℝ) ≤ (1 + α) * Real.sqrt n := by
    have h1 : 10 * (C + 1) * a ≤ 11 * C * a :=
      mul_le_mul_of_nonneg_right h10 hapos.le
    have h2 : (Y.card : ℝ) ≤ Real.sqrt n + 11 * C * a := by
      linarith [hYle, h1]
    nlinarith [h2, hαsq, hsqrt]
  -- Dichotomy (Lemma 3.3): if `|Y₀| ≤ (1-2α)√n` or `|Y| ≤ √n - 1`, the sharp
  -- tail-pairing count gives a cover of size `≤ √n`, contradiction.
  by_cases hcase : (Y₀.card : ℝ) ≤ (1 - 2 * α) * Real.sqrt n ∨
      (Y.card : ℝ) ≤ Real.sqrt n - 1
  · obtain ⟨c, F, ⟨hmono, hcov⟩, hcard⟩ :=
      tail_pairing_sharp G P hPmono Y Y₀ hYiff hY0iff
    have hY1eq : ((Y \ Y₀).card : ℝ) + Y₀.card = Y.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hY0sub
    have hbound : (1 : ℝ) + (((Y \ Y₀).card + 1) / 2 : ℕ) + Y₀.card ≤
        Real.sqrt n := by
      rcases hcase with hA | hB
      · have hdu : ((((Y \ Y₀).card + 1) / 2 : ℕ) : ℝ) ≤
            (((Y \ Y₀).card : ℝ) + 1) / 2 := by
          have h : ((((Y \ Y₀).card + 1) / 2 : ℕ) : ℝ) ≤
              (((Y \ Y₀).card + 1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) :=
            Nat.cast_div_le
          push_cast at h
          linarith
        have hαs3 : (3 : ℝ) ≤ α * Real.sqrt n := by
          have h3 : (3 : ℝ) ≤ 11 * C := by rw [hCdef]; norm_num
          have h4 := mul_le_mul h3 ha1 (by norm_num : (0 : ℝ) ≤ 1)
            (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 11) hCpos))
          nlinarith [h4, hαsq]
        nlinarith [hdu, hY1eq, hA, hYbound, hαs3]
      · have hdu : ((((Y \ Y₀).card + 1) / 2 : ℕ) : ℝ) ≤
            ((Y \ Y₀).card : ℝ) := by
          have h2 : ((Y \ Y₀).card + 1) / 2 ≤ (Y \ Y₀).card := by omega
          exact_mod_cast h2
        nlinarith [hdu, hY1eq, hB]
    exact absurd ⟨c, F, ⟨hmono, hcov⟩, le_trans hcard hbound⟩ hG
  push_neg at hcase
  obtain ⟨hY0gt, hYgt⟩ := hcase
  -- The bipartite `γ.other`-coloured graph between `X` and `Y`.
  set H := adjXYGraph G hdisjXY γ.other with hHdef
  have hbip : BipartiteOn H X Y :=
    ⟨hdisjXY, fun a b h ↦ bip_ramsey_path.Color.adjXY.across
      (show Color.adjXY G X Y γ.other a b from h)⟩
  set Yf := fullNbr H Y X with hYfdef
  set Y₁ := Y \ Yf with hY1def
  set X₀ := fullNbr H X Y with hX0def
  set X₁ := X \ X₀ with hX1def
  -- `Y₀ ⊆ Yf`: a vertex with no `γ`-edge to `P` has full `H`-degree.
  have hY0Yf : Y₀ ⊆ Yf := by
    intro y hy
    have hyY : y ∈ Y := hY0sub hy
    rw [hY0iff y] at hy
    obtain ⟨hyP, hyadj⟩ := hy
    rw [hYfdef, mem_fullNbr]
    refine ⟨hyY, ?_⟩
    have hsup : H.neighborFinset y ⊆ X := fun z hz ↦
      (bip_ramsey_path.Color.adjXY.right_mem_iff hdisjXY
        (show Color.adjXY G X Y γ.other y z from
          (H.mem_neighborFinset _ _).mp hz)).mp hyY
    have hsub : X ⊆ H.neighborFinset y := by
      intro x hx
      have hxP : x ∈ P.toList := by
        rw [hXdef] at hx
        exact List.mem_toFinset.mp hx
      have hne : x ≠ y := fun e ↦ by subst e; exact hyP hxP
      have hnadj : ¬ Color.adj G γ x y := hyadj x hxP
      have hadj : Color.adj G γ.other x y :=
        (Color.adj_iff_not_adj_other G (c := γ.other) hne).mpr
          (show ¬ Color.adj G γ.other.other x y by
            rw [Color.other_other]; exact hnadj)
      rw [SimpleGraph.mem_neighborFinset]
      show Color.adjXY G X Y γ.other y x
      exact adjXY_of_across_adj G (Or.inr ⟨hyY, hx⟩) (Color.adj_symm G hadj)
    have heq : H.neighborFinset y = X :=
      Finset.eq_of_subset_of_card_le hsup (Finset.card_le_card hsub)
    rw [heq]
  -- `|Y₁| ≤ |Y| - |Y₀| < 3α√n = 33Ca`.
  have hY1sub : Y₁ ⊆ Y \ Y₀ := by
    intro y hy
    rw [hY1def, Finset.mem_sdiff] at hy
    rw [Finset.mem_sdiff]
    exact ⟨hy.1, fun h ↦ hy.2 (hY0Yf h)⟩
  have hY1le : (Y₁.card : ℝ) ≤ (Y.card : ℝ) - Y₀.card := by
    have h1 : Y₁.card ≤ (Y \ Y₀).card := Finset.card_le_card hY1sub
    have h2 : (Y \ Y₀).card = Y.card - Y₀.card :=
      Finset.card_sdiff_of_subset hY0sub
    have h3 : ((Y \ Y₀).card : ℝ) = (Y.card : ℝ) - Y₀.card := by
      rw [h2, Nat.cast_sub (Finset.card_le_card hY0sub)]
    linarith [show (Y₁.card : ℝ) ≤ ((Y \ Y₀).card : ℝ) by exact_mod_cast h1]
  have hY1bound : (Y₁.card : ℝ) ≤ 33 * C * a := by
    nlinarith [hY1le, hYbound, hY0gt, hαsq]
  -- Every `x ∈ X₁` has a `γ`-edge to some `y ∈ Y₁`.
  have hX1edge : ∀ x ∈ X₁, ∃ y ∈ Y₁, Color.adj G γ x y := by
    intro x hx
    rw [hX1def, Finset.mem_sdiff] at hx
    obtain ⟨hxX, hxnot⟩ := hx
    have hxfull : ¬ (H.neighborFinset x).card = Y.card := by
      intro hc
      exact hxnot ((mem_fullNbr H).mpr ⟨hxX, hc⟩)
    have hnotall : ∃ y ∈ Y, ¬ H.Adj x y := by
      by_contra hall
      push_neg at hall
      have hsub : Y ⊆ H.neighborFinset x :=
        fun y hy ↦ (H.mem_neighborFinset _ _).mpr (hall y hy)
      have hsup : H.neighborFinset x ⊆ Y := fun z hz ↦
        (bip_ramsey_path.Color.adjXY.left_mem_iff hdisjXY
          (show Color.adjXY G X Y γ.other x z from
            (H.mem_neighborFinset _ _).mp hz)).mp hxX
      have heq : H.neighborFinset x = Y :=
        Finset.eq_of_subset_of_card_le hsup (Finset.card_le_card hsub)
      exact hxfull (congrArg Finset.card heq)
    obtain ⟨y, hyY, hnadjH⟩ := hnotall
    have hne : x ≠ y := fun e ↦ by
      subst e
      exact (Finset.disjoint_left.mp hdisjXY hxX) hyY
    have hnadj' : ¬ Color.adj G γ.other x y := fun h ↦
      hnadjH (adjXY_of_across_adj G (Or.inl ⟨hxX, hyY⟩) h)
    have hadj : Color.adj G γ x y :=
      (Color.adj_iff_not_adj_other G hne).mpr hnadj'
    have hyY1 : y ∈ Y₁ := by
      rw [hY1def, Finset.mem_sdiff]
      refine ⟨hyY, fun hyf ↦ ?_⟩
      rw [hYfdef, mem_fullNbr] at hyf
      obtain ⟨-, hcard⟩ := hyf
      have hsup : H.neighborFinset y ⊆ X := fun z hz ↦
        (bip_ramsey_path.Color.adjXY.right_mem_iff hdisjXY
          (show Color.adjXY G X Y γ.other y z from
            (H.mem_neighborFinset _ _).mp hz)).mp hyY
      have heq : H.neighborFinset y = X :=
        Finset.eq_of_subset_of_card_le hsup (le_of_eq hcard.symm)
      exact hnadjH (((H.mem_neighborFinset _ _).mp (heq.symm ▸ hxX)).symm)
    exact ⟨y, hyY1, hadj⟩
  -- `|X₁| ≤ |Y₁| · 2(C+1)√n ≤ 67 C² a³`, by counting `γ`-edges `X₁–Y₁`.
  have hX1bound : (X₁.card : ℝ) ≤
      (Y₁.card : ℝ) * (2 * (C + 1) * Real.sqrt n) := by
    have hsub : X₁ ⊆ Y₁.biUnion
        (fun y ↦ X₁.filter (fun x ↦ Color.adj G γ x y)) := by
      intro x hx
      obtain ⟨y, hy, hadj⟩ := hX1edge x hx
      rw [Finset.mem_biUnion]
      exact ⟨y, hy, Finset.mem_filter.mpr ⟨hx, hadj⟩⟩
    have hcard1 : X₁.card ≤ (Y₁.biUnion _).card := Finset.card_le_card hsub
    have hcard2 : (Y₁.biUnion _).card ≤
        Y₁.sum (fun y ↦ (X₁.filter fun x ↦ Color.adj G γ x y).card) :=
      Finset.card_biUnion_le
    have hfib : ∀ y ∈ Y₁,
        ((X₁.filter fun x ↦ Color.adj G γ x y).card : ℝ) ≤
          2 * (C + 1) * Real.sqrt n := by
      intro y hy
      have hyY : y ∈ Y := (Finset.mem_sdiff.mp (hY1def ▸ hy)).1
      have hyP : y ∉ P.toList := (hYiff y).mp hyY
      have hB := hNbrs y hyP
      have hset : {x : Fin n | x ∈ P.toList ∧ Color.adj G γ x y} =
          ((X.filter fun x ↦ Color.adj G γ x y) : Set (Fin n)) := by
        ext x
        simp [hXdef, Finset.coe_filter, List.mem_toFinset]
      rw [hset, Set.ncard_coe_finset] at hB
      have hsub2 : X₁.filter (fun x ↦ Color.adj G γ x y) ⊆
          X.filter (fun x ↦ Color.adj G γ x y) := by
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨(Finset.sdiff_subset (hX1def ▸ hz.1)), hz.2⟩
      exact le_trans (by exact_mod_cast Finset.card_le_card hsub2) hB
    have hsum : ((Y₁.sum fun y ↦
        (X₁.filter fun x ↦ Color.adj G γ x y).card : ℕ) : ℝ) ≤
        (Y₁.card : ℝ) * (2 * (C + 1) * Real.sqrt n) := by
      rw [Nat.cast_sum]
      calc ∑ y ∈ Y₁, ((X₁.filter fun x ↦ Color.adj G γ x y).card : ℝ)
          ≤ ∑ _y ∈ Y₁, 2 * (C + 1) * Real.sqrt n :=
            Finset.sum_le_sum fun y hy ↦ hfib y hy
        _ = Y₁.card * (2 * (C + 1) * Real.sqrt n) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have h12 : (X₁.card : ℝ) ≤
        (Y₁.sum fun y ↦ (X₁.filter fun x ↦ Color.adj G γ x y).card : ℕ) := by
      exact_mod_cast le_trans hcard1 hcard2
    linarith [h12, hsum]
  have h67 : 66 * C * (C + 1) ≤ 67 * C ^ 2 := by rw [hCdef]; norm_num
  have hX1b : (X₁.card : ℝ) ≤ 67 * C ^ 2 * a ^ 3 := by
    have hb : 2 * (C + 1) * Real.sqrt n = 2 * (C + 1) * a ^ 2 := by rw [← ha2]
    have h1 : (Y₁.card : ℝ) * (2 * (C + 1) * Real.sqrt n) ≤
        (33 * C * a) * (2 * (C + 1) * a ^ 2) := by
      rw [hb]
      exact mul_le_mul_of_nonneg_right hY1bound
        (mul_nonneg (mul_nonneg (by norm_num)
          (add_nonneg hCpos.le zero_le_one)) (pow_nonneg hapos.le 2))
    have h2 : (33 * C * a) * (2 * (C + 1) * a ^ 2) =
        66 * C * (C + 1) * a ^ 3 := by ring
    calc (X₁.card : ℝ) ≤ (Y₁.card : ℝ) * (2 * (C + 1) * Real.sqrt n) := hX1bound
      _ ≤ (33 * C * a) * (2 * (C + 1) * a ^ 2) := h1
      _ = 66 * C * (C + 1) * a ^ 3 := h2
      _ ≤ 67 * C ^ 2 * a ^ 3 :=
          mul_le_mul_of_nonneg_right h67 (pow_nonneg hapos.le 3)
  -- `|X₀| = |X| - |X₁| ≥ n/2`.
  have hX0sub : X₀ ⊆ X := by rw [hX0def]; exact Finset.filter_subset _ _
  have hX0card : (X₀.card : ℝ) = (X.card : ℝ) - X₁.card := by
    have h1 : X₁.card + X₀.card = X.card := by
      rw [hX1def]
      exact Finset.card_sdiff_add_card_eq_card hX0sub
    have h2 : (X₁.card : ℝ) + (X₀.card : ℝ) = X.card := by exact_mod_cast h1
    linarith
  have h67b : 67 * C ^ 2 * a ^ 3 ≤ a ^ 4 / 4 := by
    have hnum : (268 : ℝ) * (20 ^ 4) ^ 2 < 20 ^ 10 := by norm_num
    have h1 : (268 : ℝ) * C ^ 2 ≤ a := by
      rw [hCdef]
      nlinarith [hnum, ha20]
    have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hapos.le 3)
    have h3 : a * a ^ 3 = a ^ 4 := by ring
    nlinarith [h2, h3]
  have hYsmall : (1 + α) * Real.sqrt n ≤ a ^ 4 / 4 := by
    have hα14 : 1 + α ≤ 5 / 4 := by linarith [hαlt]
    have h1 : (1 + α) * Real.sqrt n ≤ (5 / 4) * a ^ 2 := by
      rw [← ha2]
      exact mul_le_mul_of_nonneg_right hα14 (pow_nonneg hapos.le 2)
    have h2 : (5 : ℝ) / 4 * a ^ 2 ≤ a ^ 4 / 4 := by
      have h3 := mul_nonneg (pow_nonneg hapos.le 2) (sub_nonneg.mpr ha2big)
      nlinarith [h3]
    linarith [h1, h2]
  have hX0bound : (n : ℝ) / 2 ≤ (X₀.card : ℝ) := by
    have h1 : (Y.card : ℝ) ≤ a ^ 4 / 4 := hYbound.trans hYsmall
    have h2 : (X₁.card : ℝ) ≤ a ^ 4 / 4 := hX1b.trans h67b
    rw [hX0card, hXcardR]
    nlinarith [h1, h2, ha4]
  -- `|Yf| ≥ |Y₀| > (1 - 2α) √n ≥ √n/2`.
  have hYfbound : Real.sqrt n / 2 ≤ ((fullNbr H Y X).card : ℝ) := by
    have h1 : (Y₀.card : ℝ) ≤ ((fullNbr H Y X).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hY0Yf
    have h12 : (1 : ℝ) / 2 ≤ 1 - 2 * α := by linarith [hαlt]
    have h2 := mul_le_mul_of_nonneg_right h12 hsqrt.le
    nlinarith [h1, h2, hY0gt]
  have hYfne : (fullNbr H Y X).Nonempty := by
    have h1 : (0 : ℝ) < ((fullNbr H Y X).card : ℝ) := by
      linarith [hYfbound, hsqrt]
    exact Finset.card_pos.mp (by exact_mod_cast h1)
  have hcardXY : Y.card < X.card := by
    have h1 : (Y.card : ℝ) < (X.card : ℝ) := by
      rw [hXcardR]
      have h2 : (Y.card : ℝ) ≤ a ^ 4 / 4 := hYbound.trans hYsmall
      nlinarith [h2, ha4, hapos]
    exact_mod_cast h1
  -- The `hcond` disjunction of Lemma 2.4.
  have hcond : (X \ X₀ = ∅ ∧ Y \ Yf = ∅) ∨
      ((X₀.card : ℝ) / (Y₁.card : ℝ) >
        2 * (X₁.card : ℝ) / ((fullNbr H Y X).card : ℝ)) := by
    by_cases hY1e : Y₁ = ∅
    · left
      have hYYf : Y ⊆ Yf :=
        Finset.sdiff_eq_empty_iff_subset.mp (hY1def ▸ hY1e)
      have hXX0 : X ⊆ X₀ := by
        intro x hxX
        rw [hX0def, mem_fullNbr]
        refine ⟨hxX, ?_⟩
        have hYsub : Y ⊆ H.neighborFinset x := by
          intro y hy
          have hyf := hYYf hy
          rw [hYfdef, mem_fullNbr] at hyf
          obtain ⟨-, hcard⟩ := hyf
          have hsup : H.neighborFinset y ⊆ X := fun z hz ↦
            (bip_ramsey_path.Color.adjXY.right_mem_iff hdisjXY
              (show Color.adjXY G X Y γ.other y z from
                (H.mem_neighborFinset _ _).mp hz)).mp hy
          have heq : H.neighborFinset y = X :=
            Finset.eq_of_subset_of_card_le hsup (le_of_eq hcard.symm)
          rw [SimpleGraph.mem_neighborFinset]
          exact ((H.mem_neighborFinset _ _).mp (heq.symm ▸ hxX)).symm
        have hsup' : H.neighborFinset x ⊆ Y := fun z hz ↦
          (bip_ramsey_path.Color.adjXY.left_mem_iff hdisjXY
            (show Color.adjXY G X Y γ.other x z from
              (H.mem_neighborFinset _ _).mp hz)).mp hxX
        exact congrArg Finset.card
          (Finset.eq_of_subset_of_card_le hsup' (Finset.card_le_card hYsub))
      exact ⟨Finset.sdiff_eq_empty_iff_subset.mpr hXX0, hY1e⟩
    · right
      have hY1pos : (0 : ℝ) < (Y₁.card : ℝ) := by
        have h : 0 < Y₁.card := Finset.card_pos.mpr
          (Finset.nonempty_iff_ne_empty.mpr hY1e)
        exact_mod_cast h
      have hYfpos : (0 : ℝ) < ((fullNbr H Y X).card : ℝ) := by
        linarith [hYfbound, hsqrt]
      -- `2 |X₁| |Y₁| < |X₀| |Yf|`, the cross-multiplied ratio condition.
      have hL : 2 * (X₁.card : ℝ) * (Y₁.card : ℝ) ≤ 4422 * C ^ 3 * a ^ 4 := by
        have hA : 2 * (X₁.card : ℝ) ≤ 2 * (67 * C ^ 2 * a ^ 3) :=
          mul_le_mul_of_nonneg_left hX1b (by norm_num)
        have hB : (0 : ℝ) ≤ 2 * (67 * C ^ 2 * a ^ 3) := by
          have h1 := mul_nonneg (pow_nonneg hCpos.le 2) (pow_nonneg hapos.le 3)
          nlinarith [h1]
        have hmul := mul_le_mul hA hY1bound (Nat.cast_nonneg _) hB
        have heq : 2 * (67 * C ^ 2 * a ^ 3) * (33 * C * a) =
            4422 * C ^ 3 * a ^ 4 := by ring
        linarith [hmul]
      have hR : (n : ℝ) / 2 * (Real.sqrt n / 2) ≤
          (X₀.card : ℝ) * ((fullNbr H Y X).card : ℝ) :=
        mul_le_mul hX0bound hYfbound (by positivity) (Nat.cast_nonneg _)
      have hR' : (n : ℝ) / 2 * (Real.sqrt n / 2) = a ^ 6 / 4 := by
        rw [← ha2, ← ha4]; ring
      have hRlt : 4422 * C ^ 3 * a ^ 4 < a ^ 6 / 4 := by
        have hnum : (17688 : ℝ) * (20 ^ 4) ^ 3 < 20 ^ 20 := by norm_num
        have ha2gt : (20 : ℝ) ^ 20 < a ^ 2 := by
          have h1 : (20 : ℝ) ^ 10 * (20 : ℝ) ^ 10 < (20 : ℝ) ^ 10 * a :=
            mul_lt_mul_of_pos_left ha20 (by norm_num)
          have h2 : (20 : ℝ) ^ 10 * a < a * a :=
            mul_lt_mul_of_pos_right ha20 hapos
          nlinarith [h1, h2]
        have h1 : (17688 : ℝ) * C ^ 3 < a ^ 2 := by
          rw [hCdef]
          nlinarith [hnum, ha2gt]
        have h2 := mul_lt_mul_of_pos_right h1 (pow_pos hapos 4)
        nlinarith [h2]
      have hfinal : 2 * (X₁.card : ℝ) * (Y₁.card : ℝ) <
          (X₀.card : ℝ) * ((fullNbr H Y X).card : ℝ) :=
        lt_of_le_of_lt hL (lt_of_lt_of_le (hR'.symm ▸ hRlt) hR)
      rw [gt_iff_lt, div_lt_div_iff₀ hYfpos hY1pos]
      exact hfinal
  -- Lemma 2.4: `⌊n / (|Y|+1)⌋ < √n` paths of colour `γ.other` cover `X ∪ Y`.
  obtain ⟨P_fam, hPf_chain, hPf_cov, hPf_card⟩ :=
    refined_path_cover H X Y hbip hcardXY hYfne hcond
  have hPfmono : ∀ p ∈ P_fam, p.IsMonochromatic G γ.other := fun p hp ↦
    (hPf_chain p hp).imp fun _ _ h ↦ adjXY_to_adj G hdisjXY h
  have hcovall : ∀ v : Fin n, ∃ p ∈ P_fam, v ∈ p := by
    intro v
    have hv : v ∈ X ∪ Y := by
      by_cases hvX : v ∈ X
      · exact Finset.mem_union_left _ hvX
      · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hvX)
    exact hPf_cov v hv
  have hcardlt : (P_fam.card : ℝ) < Real.sqrt n := by
    have hXY : X.card + Y.card = n := by omega
    have h1 : P_fam.card ≤ n / (Y.card + 1) := by
      calc P_fam.card ≤ (X.card + Y.card) / (Y.card + 1) := hPf_card
        _ = n / (Y.card + 1) := by rw [hXY]
    have h2 : (P_fam.card : ℝ) ≤ (n : ℝ) / ((Y.card : ℝ) + 1) := by
      calc (P_fam.card : ℝ) ≤ ((n / (Y.card + 1) : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ ≤ (n : ℝ) / ((Y.card + 1 : ℕ) : ℝ) := Nat.cast_div_le
        _ = (n : ℝ) / ((Y.card : ℝ) + 1) := by push_cast; ring
    have h3 : (n : ℝ) / ((Y.card : ℝ) + 1) < Real.sqrt n := by
      have hY1 : Real.sqrt n < (Y.card : ℝ) + 1 := by linarith [hYgt]
      have hpos : (0 : ℝ) < (Y.card : ℝ) + 1 := by linarith [hsqrt, hY1]
      rw [div_lt_iff₀ hpos]
      calc (n : ℝ) = Real.sqrt n * Real.sqrt n :=
            (Real.mul_self_sqrt hnR.le).symm
        _ < Real.sqrt n * ((Y.card : ℝ) + 1) :=
            mul_lt_mul_of_pos_left hY1 hsqrt
    linarith [h2, h3]
  exact absurd ⟨γ.other, P_fam, ⟨hPfmono, hcovall⟩, le_of_lt hcardlt⟩ hG

end JSP415
