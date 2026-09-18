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
  sorry

/-- **PVW24 Lemma 3.3 (tail pairing).**  If `P` is a blue path, `Y = [n] ∖ V(P)`
and `Y₀ ⊆ Y` is the set of leftover vertices with no blue edge to `P`, then
`f(n,χ) < 2 + |Y|/2 + |Y₀|/2` (in fact `f ≤ 1 + ⌈|Y ∖ Y₀|/2⌉ + |Y₀|`). -/
theorem tail_pairing_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (P : VertPath (Fin n)) (hP : P.IsMonochromatic G .blue)
    (Y Y₀ : Finset (Fin n))
    (hY : ∀ y, y ∈ Y ↔ y ∉ P.toList)
    (hY0 : ∀ y, y ∈ Y₀ ↔ y ∉ P.toList ∧ ∀ x ∈ P.toList, ¬ Color.adj G .blue x y) :
    HasCoverLt G (2 + (Y.card : ℝ) / 2 + (Y₀.card : ℝ) / 2) := by
  sorry

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
