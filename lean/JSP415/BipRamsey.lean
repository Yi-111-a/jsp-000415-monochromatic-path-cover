import JSP415.GLScratchTop
import JSP415.GLScratchTight
import JSP415.GLScratchLC2
import JSP415.GLScratchGH
import JSP415.GLScratchZ
import JSP415.GLScratchF
import JSP415.GLScratchCmpl
import JSP415.GLScratchAsm
import JSP415.GLScratchE7

/-!
# JSP415/BipRamsey — final assembly of Gyárfás–Lehel Theorem 3

`bip_ramsey_path'` packages the whole case-(iii) analysis behind one remaining
input: **Claim E**, the internal red-completeness of the maximal bipath's red
branch.  Given a `claimE` theorem for every `Case3Data` with two lower
leftovers, this file produces `BipGoal` — the bipartite Ramsey alternative for
paths (PVW24 Lemma 2.1).

Claim E′ and Claim F₁ come for free via `Case3Data.compl`
(`JSP415/GLScratchCmpl.lean`); F₂ is `claimF2` (`JSP415/GLScratchF.lean`); the
leftover claims C, C′, G, H are `claimC`/`claimC'` (`GLScratchLC2`) and
`ghfacts` (`GLScratchGH`); the finale is `case3_finale` (`GLScratchZ`) inside
`bip_ramsey_of_facts` (`GLScratchTop`) with `tight_case` (`GLScratchTight`).
-/

open Finset
open Classical
namespace JSP415
open bip_ramsey_path
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

namespace Case3Data

/-- Dual transport: `ClaimE` of `c3` gives `ClaimE'` of the complemented
data (red-completeness of `S₁` becomes blue-completeness of `S₂` after
complementation and reversal). -/
theorem claimE'_of_orig (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hE : c3.ClaimE) : (c3.compl hXY).ClaimE' := by
  intro u hu l hl hlb
  rw [c3c_S2U c3 hXY] at hu
  rw [c3c_SL c3 hXY] at hl
  have hla : l ∈ c3.A ∨ l = c3.z := by
    rcases hlb with h | h
    · exact Or.inl (List.mem_reverse.mp h)
    · exact Or.inr h
  intro hcl
  rw [SimpleGraph.compl_adj] at hcl
  exact hcl.2 (hE u hu l hl hla)

end Case3Data

/-- **All case-(iii) facts from Claim E alone.**  For every `Case3Data` with
two distinct lower leftovers, the internal and leftover completeness facts
hold. -/
theorem hfacts (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    (hux2 : c3.HasUx2)
    (hEall : ∀ (H : SimpleGraph V) {X₁ Y₁ : Finset V}, Disjoint X₁ Y₁ →
      ∀ c : Case3Data H X₁ Y₁, c.HasUx2 → c.ClaimE) :
    c3.InternalFacts ∧ c3.LeftoverFacts := by
  classical
  have hE : c3.ClaimE := hEall G hXY c3 hux2
  have hEc : (c3.compl hXY).ClaimE :=
    hEall Gᶜ hXY (c3.compl hXY) (c3.c3c_ux2 hXY hux2)
  have hE' : c3.ClaimE' := c3.claimE'_of_compl hXY hEc
  have hE'c : (c3.compl hXY).ClaimE' := c3.claimE'_of_orig hXY hE
  have hF1 : ∀ u ∈ c3.S1U, ∀ l ∈ c3.SL, l ∈ c3.B → G.Adj u l :=
    c3.claimF1_of_compl hXY (claimF2 (c3.compl hXY) hXY hEc hE'c)
  have hF2 : ∀ l ∈ c3.SL, l ∈ c3.A → ∀ u ∈ c3.S2U, ¬ G.Adj l u :=
    claimF2 c3 hXY hE hE'
  have hB2 : ∀ l ∈ c3.SL, l ∈ c3.B → G.Adj (c3.A.head c3.hA) l :=
    claimB2 c3 hXY
  exact hfacts_of hXY c3 hux2 hE hE' hF1 hF2 hB2

/-- **Gyárfás–Lehel 1973, Theorem 3 = PVW24 Lemma 2.1**, modulo Claim E:
for distinct `k ℓ`, every red–blue colouring of the complete bipartite graph
`K_{m,m}`, `m = ⌊(k + ℓ + 1) / 2⌋`, contains a red `acrossXY`-chain on
`k + 1` vertices or a blue one on `ℓ + 1` vertices. -/
theorem bip_ramsey_path'
    (hEall : ∀ (H : SimpleGraph V) {X₁ Y₁ : Finset V}, Disjoint X₁ Y₁ →
      ∀ c : Case3Data H X₁ Y₁, c.HasUx2 → c.ClaimE)
    (G : SimpleGraph V) (X Y : Finset V) (hXY : Disjoint X Y) {k ℓ : ℕ}
    (hkl : k ≠ ℓ)
    (hX : X.card = (k + ℓ + 1) / 2) (hY : Y.card = (k + ℓ + 1) / 2) :
    BipGoal G X Y k ℓ :=
  bip_ramsey_path_of
    (fun H _ _ hD c3 hu2 ↦ hfacts hD c3 hu2 hEall) hXY hkl hX hY

/-- **Gyárfás–Lehel 1973, Theorem 3 = PVW24 Lemma 2.1.**  For distinct
`k ℓ`, every red–blue edge colouring of the complete bipartite graph
`K_{⌊(k+ℓ+1)/2⌋,⌊(k+ℓ+1)/2⌋}` contains a red `acrossXY`-chain on `k + 1`
vertices or a blue one on `ℓ + 1` vertices.  Claim E is
`Case3Data.claimE` (`GLScratchE7`). -/
theorem bip_ramsey_path (G : SimpleGraph V) (X Y : Finset V)
    (hXY : Disjoint X Y) {k ℓ : ℕ} (hkl : k ≠ ℓ)
    (hX : X.card = (k + ℓ + 1) / 2) (hY : Y.card = (k + ℓ + 1) / 2) :
    BipGoal G X Y k ℓ :=
  bip_ramsey_path' (fun H _ _ hD c3 hu2 ↦ c3.claimE hD hu2) G X Y hXY hkl hX hY

end JSP415
