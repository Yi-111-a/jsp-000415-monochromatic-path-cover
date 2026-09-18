import Mathlib

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
imposed separately via `List.Chain'` conditions, so the same `VertPath` may be
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
  fun p q ↦ decidable_of_iff _ ⟨VertPath.ext, congrArg VertPath.toList⟩

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
  simp [Membership.mem, singleton]

theorem mem_verts [DecidableEq V] {p : VertPath V} {v : V} : v ∈ p.verts ↔ v ∈ p :=
  List.mem_toFinset

end VertPath

/-- Adjacency of colour `c` in the colouring whose red graph is `G`:
red pairs are `G`-adjacent; blue pairs are distinct and non-`G`-adjacent. -/
def Color.adj (G : SimpleGraph V) : Color → V → V → Prop
  | .red, a, b => G.Adj a b
  | .blue, a, b => a ≠ b ∧ ¬G.Adj a b

theorem Color.adj_symm {V : Type*} (G : SimpleGraph V) {c : Color} {a b : V}
    (h : Color.adj G c a b) : Color.adj G c b a := by
  cases c with
  | red => exact G.symm h
  | blue => exact ⟨h.1.symm, fun hba ↦ h.2 (G.symm hba)⟩

/-- `p` is monochromatic of colour `c` under the colouring `G`: consecutive
vertices are `c`-adjacent. -/
def VertPath.IsMonochromatic {V : Type*} (G : SimpleGraph V) (c : Color)
    (p : VertPath V) : Prop :=
  p.toList.Chain' (Color.adj G c)

@[simp]
theorem VertPath.singleton_isMonochromatic {V : Type*} (G : SimpleGraph V)
    (c : Color) (v : V) : (VertPath.singleton v).IsMonochromatic G c := by
  simp [VertPath.IsMonochromatic, VertPath.singleton]

/-- `𝒫` covers the vertex set: every vertex lies on some path of the family. -/
def VertPath.Covers {V : Type*} (𝒫 : Finset (VertPath V)) : Prop :=
  ∀ v : V, ∃ p ∈ 𝒫, v ∈ p

/-- The full condition from the paper: a cover by paths all monochromatic in
one fixed colour `c`. -/
def IsSameColorCover {V : Type*} (G : SimpleGraph V) (c : Color)
    (𝒫 : Finset (VertPath V)) : Prop :=
  (∀ p ∈ 𝒫, p.IsMonochromatic G c) ∧ 𝒫.Covers

/-- Push a vertex path forward along an injective map. -/
def VertPath.map {V W : Type*} (f : V → W) (hf : Function.Injective f)
    (p : VertPath V) : VertPath W where
  toList := p.toList.map f
  nonempty := by simp [p.nonempty]
  nodup := p.nodup.map hf

@[simp] theorem VertPath.mem_map {V W : Type*} {f : V → W} {hf : Function.Injective f}
    {p : VertPath V} {w : W} : w ∈ p.map f hf ↔ ∃ v ∈ p, f v = w := by
  simp [VertPath.map, Membership.mem]

/-- `G` admits a same-colour monochromatic path cover of size at most `b`
(real bound). -/
def HasCoverLe {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (b : ℝ) : Prop :=
  ∃ c : Color, ∃ 𝒫 : Finset (VertPath V),
    IsSameColorCover G c 𝒫 ∧ (𝒫.card : ℝ) ≤ b

/-- `G` admits a same-colour monochromatic path cover of size strictly below
`b` (real bound). -/
def HasCoverLt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (b : ℝ) : Prop :=
  ∃ c : Color, ∃ 𝒫 : Finset (VertPath V),
    IsSameColorCover G c 𝒫 ∧ (𝒫.card : ℝ) < b

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
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hp
    obtain ⟨v, rfl⟩ := hp
    simp
  · intro v
    exact ⟨VertPath.singletonEmbedding v,
      Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩, by
      show v ∈ (VertPath.singleton v).toList; simp [VertPath.singleton]⟩
  · simp

theorem HasCoverLt.self {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {b : ℝ} (hb : (Fintype.card V : ℝ) < b) :
    HasCoverLt G b :=
  let ⟨c, 𝒫, h, hcard⟩ := HasCoverLe.self G
  ⟨c, 𝒫, h, hcard.trans_lt hb⟩

/-- Cover bounds transport along vertex equivalences: a cover of the comap
colouring pulls back to a cover of `G`.  Proof deferred to the API layer. -/
theorem HasCoverLe.comap {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph W} {f : V → W}
    (hf : Function.Injective f) (hfs : Function.Surjective f) {b : ℝ}
    (h : HasCoverLe (G.comap f) b) : HasCoverLe G b := by
  sorry

/-- The subtype induced colouring: restrict `G` to a finset of vertices. -/
def inducedColoring {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) : SimpleGraph S :=
  G.comap (Function.Embedding.subtype S)

end JSP415
