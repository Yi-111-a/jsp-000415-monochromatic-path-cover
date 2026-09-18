# JSP-000415 Solver Findings

## Verifier
`scripts/harness.sh` → HARNESS_LOG.md. Score = sorry/admit count (target 0)
then `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.

## Baseline (commit 345675d / 5eb159c)
- lake build: GREEN (with sorry warnings)
- sorries: 12 = Gerencser 2 + BipLemmas 4 + Section3 6
- axioms: [propext, sorryAx, Classical.choice, Quot.sound] → RED

## Active branches
- agent 14cb2d68: Gerencser.lean (gerencser_gyarfas + exists_mono_path_half).
  Strategy: strong induction on card V; remove v; case analysis on colours of
  v-p_last, v-q_last, p_last-q_last. No disjointness needed (overlap harmless).
- agent 9c054b25: bip_ramsey_path (Gyarfas-Lehel Lemma 2.1).

## API notes (learned)
- `decidable_of_iff (a) (h : a ↔ b)`: a = decidable side FIRST.
- `Finset.mem_map` must be `.mp`'d before rcases.
- `List.IsChain` (v4.34, was `List.Chain'`): `isChain_map`,
  `isChain_map_of_isChain`, `IsChain.append`, `.dropLast`, `.infix`.
- `G.neighborFinset` needs `Mathlib.Combinatorics.SimpleGraph.Finite`.
- Narrow imports (not `import Mathlib`) → file builds in ~10s not ~6min.

## Ruled out / dead ends
- `Finset.Covers` does not exist (use explicit ∀v ∃p∈P, v∈p).
- `HasCoverLe.comap` needs Surjective (injective-only version is false).
