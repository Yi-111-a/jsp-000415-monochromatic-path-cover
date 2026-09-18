import JSP415.Defs

/-!
# Gerencsér–Gyárfás 1967 (PVW24 Theorem 1.1)

Every 2-edge-coloured complete graph can be covered by two monochromatic
paths (of possibly different colours).
-/

namespace JSP415

/-- **Gerencsér–Gyárfás** (PVW24 Theorem 1.1).  The vertex set of every
2-edge-coloured complete graph can be covered by two monochromatic paths;
the two paths may have different colours. -/
theorem gerencser_gyarfas {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ∃ (c₁ c₂ : Color) (p q : VertPath V),
      p.IsMonochromatic G c₁ ∧ q.IsMonochromatic G c₂ ∧
      ∀ v : V, v ∈ p ∨ v ∈ q := by
  sorry

/-- Corollary form used in the proof of Lemma 3.2: some monochromatic path
covers at least half the vertices. -/
theorem exists_mono_path_half {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ∃ c : Color, ∃ p : VertPath V, p.IsMonochromatic G c ∧
      Fintype.card V ≤ 2 * p.toList.length := by
  sorry

end JSP415
