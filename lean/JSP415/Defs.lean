import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.List.Chain

/-!
# JSP-000415 — definitions layer

A red–blue edge colouring of the complete graph on `V` is represented by a
`SimpleGraph V` `G`: a pair of distinct vertices is **red** iff `G.Adj` holds,
and **blue** otherwise.

Paths are represented as vertex lists (`VertPath`) rather than
`SimpleGraph.Path`, because the arguments constantly reorder and splice vertex
sequences (e.g. `v₁…vᵢ vⱼ vⱼ₋₁…vᵢ₊₁ y vⱼ₊₁…vᵣ` in Lemma 3.2).
-/

open Finset

namespace JSP415

/-- The two colours of the edge colouring. -/
inductive Color : Type
  | red : Color
  | blue : Color
  deriving DecidableEq

/-- A vertex path: a nonempty list of distinct vertices.  Monochromaticity is
imposed separately via `List.IsChain` conditions, so the same `VertPath` may be
declared red- or blue-monochromatic. -/
structure VertPath (V : Type*) where
  toList : List V
  nonempty : toList ≠ []
  nodup : toList.Nodup

namespace VertPath

variable {V : Type*}

instance : Membership V (VertPath V) := ⟨fun p v ↦ v ∈ p.toList⟩

@[ext]
theorem ext {p q : VertPath V} (h : p.toList = q.toList) : p = q := by
  cases p; cases q; simp_all

instance [DecidableEq V] : DecidableEq (VertPath V) :=
  fun p q ↦ decidable_of_iff (p.toList = q.toList)
    ⟨VertPath.ext, congrArg VertPath.toList⟩

/-- Number of vertices of the path. -/
def card (p : VertPath V) : ℕ := p.toList.length

/-- The vertex set of a path as a finset. -/
def verts [DecidableEq V] (p : VertPath V) : Finset V := p.toList.toFinset

/-- The singleton path on `v` (the paper's "length 0" path). -/
def singleton (v : V) : VertPath V where
  toList := [v]
  nonempty := by simp
  nodup := by simp

@[simp] theorem mem_singleton {v w : V} : v ∈ (singleton w) ↔ v = w := by
  show v ∈ [w] ↔ v = w
  simp

theorem mem_verts [DecidableEq V] {p : VertPath V} {v : V} : v ∈ p.verts ↔ v ∈ p :=
  List.mem_toFinset

end VertPath

/-- Adjacency of colour `c` in the colouring whose red graph is `G`:
red pairs are `G`-adjacent; blue pairs are distinct and non-`G`-adjacent. -/
def Color.adj {V : Type*} (G : SimpleGraph V) : Color → V → V → Prop
  | .red, a, b => G.Adj a b
  | .blue, a, b => a ≠ b ∧ ¬G.Adj a b

theorem Color.adj_symm {V : Type*} (G : SimpleGraph V) {c : Color} {a b : V}
    (h : Color.adj G c a b) : Color.adj G c b a := by
  cases c with
  | red => exact h.symm
  | blue => exact ⟨h.1.symm, fun hba ↦ h.2 hba.symm⟩

theorem Color.adj_comap {V W : Type*} (G : SimpleGraph W) {f : V → W}
    (hf : Function.Injective f) {c : Color} {a b : V}
    (h : Color.adj (G.comap f) c a b) : Color.adj G c (f a) (f b) := by
  cases c with
  | red => exact h
  | blue => exact ⟨fun hfb ↦ h.1 (hf hfb), h.2⟩

/-- `p` is monochromatic of colour `c` under the colouring `G`: consecutive
vertices are `c`-adjacent. -/
def VertPath.IsMonochromatic {V : Type*} (G : SimpleGraph V) (c : Color)
    (p : VertPath V) : Prop :=
  p.toList.IsChain (Color.adj G c)

@[simp]
theorem VertPath.singleton_isMonochromatic {V : Type*} (G : SimpleGraph V)
    (c : Color) (v : V) : (VertPath.singleton v).IsMonochromatic G c :=
  List.isChain_singleton v

/-- `P` covers the vertex set: every vertex lies on some path of the family. -/
def VertPath.Covers {V : Type*} (P : Finset (VertPath V)) : Prop :=
  ∀ v : V, ∃ p ∈ P, v ∈ p

/-- The full condition from the paper: a cover by paths all monochromatic in
one fixed colour `c`. -/
def IsSameColorCover {V : Type*} (G : SimpleGraph V) (c : Color)
    (P : Finset (VertPath V)) : Prop :=
  (∀ p ∈ P, p.IsMonochromatic G c) ∧ VertPath.Covers P

/-- Push a vertex path forward along an injective map. -/
def VertPath.map {V W : Type*} (f : V → W) (hf : Function.Injective f)
    (p : VertPath V) : VertPath W where
  toList := p.toList.map f
  nonempty := fun h ↦ p.nonempty (List.map_eq_nil_iff.mp h)
  nodup := p.nodup.map hf

@[simp] theorem VertPath.mem_map {V W : Type*} {f : V → W} {hf : Function.Injective f}
    {p : VertPath V} {w : W} : w ∈ p.map f hf ↔ ∃ v ∈ p, f v = w := by
  show w ∈ (p.map f hf).toList ↔ ∃ v, v ∈ p.toList ∧ f v = w
  simp [VertPath.map]

theorem VertPath.IsMonochromatic.map {V W : Type*} {G : SimpleGraph W}
    {f : V → W} (hf : Function.Injective f) {c : Color} {p : VertPath V}
    (h : p.IsMonochromatic (G.comap f) c) : (p.map f hf).IsMonochromatic G c :=
  List.isChain_map_of_isChain f (fun _ _ ↦ Color.adj_comap G hf) h

/-- `G` admits a same-colour monochromatic path cover of size at most `b`
(real bound). -/
def HasCoverLe {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (b : ℝ) : Prop :=
  ∃ c : Color, ∃ P : Finset (VertPath V),
    IsSameColorCover G c P ∧ (P.card : ℝ) ≤ b

/-- `G` admits a same-colour monochromatic path cover of size strictly below
`b` (real bound). -/
def HasCoverLt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (b : ℝ) : Prop :=
  ∃ c : Color, ∃ P : Finset (VertPath V),
    IsSameColorCover G c P ∧ (P.card : ℝ) < b

/-- Every red–blue colouring of every `m`-vertex complete graph admits a
same-colour cover of size at most `b`.  Quantifying over all vertex types is
what lets the induction hypothesis be applied to induced subgraphs (e.g.
vertex subsets of `Fin n`). -/
def AllCoverLe (m : ℕ) (b : ℝ) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W = m →
    ∀ G : SimpleGraph W, HasCoverLe G b

/-- Every red–blue colouring of every `m`-vertex complete graph admits a
same-colour cover of size strictly below `b`. -/
def AllCoverLt (m : ℕ) (b : ℝ) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W = m →
    ∀ G : SimpleGraph W, HasCoverLt G b

/-- Embedding of vertices into singleton paths. -/
def VertPath.singletonEmbedding {V : Type*} : V ↪ VertPath V where
  toFun := VertPath.singleton
  inj' := fun a b h ↦ by
    have := congrArg VertPath.toList h
    simpa [VertPath.singleton] using this

/-- Trivial bound: the singleton paths cover `K_V` with `|V|` paths of any
colour.  This also shows `HasCoverLe`/`HasCoverLt` bounds are always
attainable, i.e. a minimum `f(n, χ)` exists in the paper's language. -/
theorem HasCoverLe.self {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    HasCoverLe G (Fintype.card V : ℝ) := by
  classical
  refine ⟨.red, Finset.univ.map VertPath.singletonEmbedding, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hp
    exact List.isChain_singleton v
  · intro v
    refine ⟨VertPath.singletonEmbedding v,
      Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩, ?_⟩
    show v ∈ [v]
    simp
  · simp

theorem HasCoverLt.self {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {b : ℝ} (hb : (Fintype.card V : ℝ) < b) :
    HasCoverLt G b :=
  let ⟨c, P, h, hcard⟩ := HasCoverLe.self G
  ⟨c, P, h, lt_of_le_of_lt hcard hb⟩

/-- Cover bounds transport along vertex bijections: a cover of the comap
colouring pushes forward along a bijection to a cover of `G`. -/
theorem HasCoverLe.comap {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph W} {f : V → W}
    (hf : Function.Injective f) (hfs : Function.Surjective f) {b : ℝ}
    (h : HasCoverLe (G.comap f) b) : HasCoverLe G b := by
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

/-- The subtype induced colouring: restrict `G` to a finset of vertices. -/
def inducedColoring {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) : SimpleGraph S :=
  G.comap Subtype.val

end JSP415
