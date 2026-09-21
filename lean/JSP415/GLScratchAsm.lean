import JSP415.GLScratchTop
import JSP415.GLScratchTight
import JSP415.GLScratchLC2
import JSP415.GLScratchGH
import JSP415.GLScratchZ

/-!
# `GLScratchAsm` — pointwise assembly + parameterized reduction

* `hfacts_of`: assembles `InternalFacts ∧ LeftoverFacts` for a `Case3Data`
  from the case-(iii) claims `E`, `E′`, `F`, `B₂` (the `B₂`/cross-`F`
  ingredients arrive as hypotheses while `GLScratchF` is being repaired).
* `bip_ramsey_path_of`: the parameterized top-level reduction — given a
  supplier `hfacts` of the case-(iii) facts for every `Case3Data`, the
  Ramsey alternative `BipGoal` follows via `bip_ramsey_of_facts` with the
  tight-parity subcase discharged by `tight_case`.
-/

open Finset
open Classical
namespace JSP415
open bip_ramsey_path
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

/-- Pointwise assembly of the case-(iii) facts: internal completeness
(`E`+`E′`+`F`) plus the leftover facts (`C` from `claimB'`, `C′` from `hB2`,
`G`/`H` from `ghfacts`). -/
theorem hfacts_of (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    (hux2 : c3.HasUx2)
    (hE : c3.ClaimE) (hE' : c3.ClaimE')
    (hF1 : ∀ u ∈ c3.S1U, ∀ l ∈ c3.SL, l ∈ c3.B → G.Adj u l)
    (hF2 : ∀ l ∈ c3.SL, l ∈ c3.A → ∀ u ∈ c3.S2U, ¬ G.Adj l u)
    (hB2 : ∀ l ∈ c3.SL, l ∈ c3.B → G.Adj (c3.A.head c3.hA) l) :
    c3.InternalFacts ∧ c3.LeftoverFacts := by
  have hI : c3.InternalFacts :=
    c3.internalFacts_of_E_F hE hE' ⟨hF1, hF2⟩
  have hC : c3.LeftoverC :=
    ⟨claimC hXY c3 (claimB' hXY c3), claimC' hXY c3 hB2⟩
  have hGH : c3.GHfacts := ghfacts c3 hXY hI hC hux2
  exact ⟨hI, c3.leftoverFacts_of_C_GH hC hGH⟩

/-- The parameterized top-level reduction: given a supplier `hfacts` of the
internal and leftover facts for every `Case3Data`, `BipGoal` holds.  The
tight-parity branch (`¬ HasUx2`) is discharged by `tight_case`. -/
theorem bip_ramsey_path_of
    (hfacts : ∀ (H : SimpleGraph V) {X₁ Y₁ : Finset V}, Disjoint X₁ Y₁ →
      ∀ c3 : Case3Data H X₁ Y₁, c3.HasUx2 →
        c3.InternalFacts ∧ c3.LeftoverFacts)
    (hXY : Disjoint X Y) {k ℓ : ℕ} (hkl : k ≠ ℓ)
    (hX : X.card = (k + ℓ + 1) / 2) (hY : Y.card = (k + ℓ + 1) / 2) :
    BipGoal G X Y k ℓ := by
  refine bip_ramsey_of_facts hfacts ?_ hXY hkl hX hY
  intro H' X₁ Y₁ c3 hD hn k' ℓ' hkl' hX' hY'
  exact c3.tight_case hD hn hkl' hX' hY'

end JSP415
