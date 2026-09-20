import JSP415.GLIface
import JSP415.GLScratchA
import JSP415.GLScratchD

/-!
# `bip_ramsey_path_T5` — Gyárfás–Lehel 1973 Thm 3 (independent attempt)

Goal: disjoint `X Y`, `|X| = |Y| = (k+ℓ+1)/2`, `k ≠ ℓ` ⇒
∃ `VertPath`, red `Color.adjXY` chain on ≥ k+1 vertices or blue on ≥ ℓ+1.

Strategy (this file's own route):

* Reduce by complement/side-swap to a maximal *red-first* bipath
  `S = A ++ z :: B` with `z ∈ X`.
* If `S` covers `X ∪ Y`, `bipath_cover` finishes.
* Degenerate cases (`A = []` or `B = []`): any `Y`-leftover yields a
  strictly longer either-order bipath (elementary surgery), so `Y ⊆ S`
  and side-counting shows the single-colour branch already reaches the
  goal length.
* If `Y ⊆ S` but `X ∖ S ≠ ∅` (the "parity subcase"), counting forces
  `|A| = k-1`, `|B| = ℓ-1`, `X ∖ S = {ux}`, endpoints in `Y`; a chain of
  forced edge colours (`ux–a₁` blue, `ux–bₛ` red, `z–bₛ` blue, `a₁–z`
  red, `a₂–b₁` red) closes the goal by explicit paths.
* Otherwise a `Y`-leftover exists; the killing lemmas force endpoints
  into `Y`, producing `Case3Data`; `InternalFacts`/`LeftoverFacts`
  (the GL rotation claims) feed `two_block_ramsey`.
-/

open Finset
open Classical

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

/-! ### Goal constructors and transports -/

/-- Any vertex gives a `VertPath` singleton; a chain goal of length `1`
is trivially satisfied. -/
theorem bip_goal_singleton_red (G : SimpleGraph V) (X Y : Finset V) (v : V) :
    ∃ p : VertPath V, p.toList.IsChain (Color.adjXY G X Y .red) ∧
      1 ≤ p.toList.length :=
  ⟨VertPath.singleton v, List.isChain_singleton v, by simp [VertPath.singleton]⟩

theorem bip_goal_singleton_blue (G : SimpleGraph V) (X Y : Finset V) (v : V) :
    ∃ p : VertPath V, p.toList.IsChain (Color.adjXY G X Y .blue) ∧
      1 ≤ p.toList.length :=
  ⟨VertPath.singleton v, List.isChain_singleton v, by simp [VertPath.singleton]⟩

/-- Transport the goal across `X ↔ Y`. -/
theorem bipGoal_swapXY {G : SimpleGraph V} {X Y : Finset V} {k ℓ : ℕ}
    (h : BipGoal G X Y k ℓ) : BipGoal G Y X k ℓ := by
  obtain ⟨p, h | h⟩ := h
  · exact ⟨p, Or.inl ⟨(isChain_swapXY).mpr h.1, h.2⟩⟩
  · exact ⟨p, Or.inr ⟨(isChain_swapXY).mpr h.1, h.2⟩⟩

/-- Transport the goal across `G ↔ Gᶜ` (with `k ↔ ℓ`). -/
theorem bipGoal_compl {G : SimpleGraph V} {X Y : Finset V} {k ℓ : ℕ}
    (hXY : Disjoint X Y) (h : BipGoal Gᶜ X Y ℓ k) : BipGoal G X Y k ℓ := by
  obtain ⟨p, h | h⟩ := h
  · exact ⟨p, Or.inr ⟨chain_blue_of_compl_red hXY h.1, h.2⟩⟩
  · exact ⟨p, Or.inl ⟨chain_red_of_compl_blue hXY h.1, h.2⟩⟩

/-- A red `acrossXY` edge gives a 2-vertex red path (settles `k = 1`). -/
theorem bip_goal_red_edge {G : SimpleGraph V} {X Y : Finset V}
    (hXY : Disjoint X Y) {a b : V} (h : Color.adjXY G X Y .red a b) :
    ∃ p : VertPath V, p.toList.IsChain (Color.adjXY G X Y .red) ∧
      2 ≤ p.toList.length := by
  refine ⟨⟨[a, b], by simp, ?_⟩, ?_, by simp⟩
  · simp only [List.nodup_cons, List.mem_singleton, List.nodup_nil, and_true]
    exact ⟨fun hab ↦ (acrossXY.ne hXY h.1) hab, by simp⟩
  · rw [List.isChain_cons]
    exact ⟨fun y hy ↦ by
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hy; exact h, List.isChain_singleton b⟩

/-- A blue `acrossXY` edge gives a 2-vertex blue path (settles `ℓ = 1`). -/
theorem bip_goal_blue_edge {G : SimpleGraph V} {X Y : Finset V}
    (hXY : Disjoint X Y) {a b : V} (h : Color.adjXY G X Y .blue a b) :
    ∃ p : VertPath V, p.toList.IsChain (Color.adjXY G X Y .blue) ∧
      2 ≤ p.toList.length := by
  refine ⟨⟨[a, b], by simp, ?_⟩, ?_, by simp⟩
  · simp only [List.nodup_cons, List.mem_singleton, List.nodup_nil, and_true]
    exact ⟨fun hab ↦ (acrossXY.ne hXY h.1) hab, by simp⟩
  · rw [List.isChain_cons]
    exact ⟨fun y hy ↦ by
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hy; exact h, List.isChain_singleton b⟩

end JSP415
