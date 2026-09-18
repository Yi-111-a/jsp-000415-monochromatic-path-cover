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
strong bound at level `n`. -/
theorem overlap_bound {n : ℕ} {C₁ C₂ : ℝ}
    (hind : ∀ m < n, AllCoverLt m (Real.sqrt m + C₁))
    (G : SimpleGraph (Fin n)) {k : ℕ}
    (PR : Fin k → VertPath (Fin n)) (hPR : ∀ i, (PR i).IsMonochromatic G .red)
    (QB : Fin k → VertPath (Fin n)) (hQB : ∀ i, (QB i).IsMonochromatic G .blue)
    (S : Finset (Fin n))
    (hS : ∀ s ∈ S, (∃ i, s ∈ PR i) ∧ (∃ i, s ∈ QB i))
    (hineq : Real.sqrt (n - S.card : ℝ) + C₁ + k ≤ Real.sqrt n + C₂) :
    HasCoverLe G (Real.sqrt n + C₂) := by
  sorry

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
  sorry

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
        ((P.toList.toFinset.filter fun x ↦ Color.adj G c x y).card : ℝ) ≤
          2 * (C₁ - C₂ + 1) * Real.sqrt n := by
  sorry

/-- **PVW24 Lemma 3.3 (tail pairing).**  If `P` is a blue path and `Y₀ ⊆ Y` is
the set of leftover vertices with no blue edge to `P`, then
`f(n,χ) ≤ 1 + ⌈|Y ∖ Y₀|/2⌉ + |Y₀| < 2 + |Y|/2 + |Y₀|/2`. -/
theorem tail_pairing_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (P : VertPath (Fin n)) (hP : P.IsMonochromatic G .blue) :
    HasCoverLe G
      (1 + ((univ.filter (· ∉ P.toList)) \
            (univ.filter fun y ↦ y ∉ P.toList ∧
              ∀ x ∈ P.toList, ¬ Color.adj G .blue x y)).card / 2 +
       ((univ.filter (· ∉ P.toList)) \
            (univ.filter fun y ↦ y ∉ P.toList ∧
              ∀ x ∈ P.toList, ¬ Color.adj G .blue x y)).card % 2 +
       (univ.filter fun y ↦ y ∉ P.toList ∧
              ∀ x ∈ P.toList, ¬ Color.adj G .blue x y).card : ℝ) := by
  sorry

/-- **PVW24 Lemma 3.3, usable form.**  With `Y = [n] ∖ V(P)` and `Y₀ ⊆ Y` the
vertices with no blue edge to `P`, `f(n,χ) < 2 + |Y|/2 + |Y₀|/2`. -/
theorem tail_pairing_bound' {n : ℕ} (G : SimpleGraph (Fin n))
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
    ∃ c : Color, ∃ 𝒫 : Finset (VertPath (Fin n)),
      IsSameColorCover G c 𝒫 ∧ (𝒫.card : ℝ) ≤ Real.sqrt n := by
  sorry

end JSP415
