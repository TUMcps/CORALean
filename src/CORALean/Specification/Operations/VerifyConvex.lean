module

public import CORALean.Specification.Definitions.VerifyAnswer
public import CORALean.Specification.Specification
public import CORALean.Global.SupportFunction.SupportFunction
public import Mathlib.Analysis.Convex.Hull
public import CORALean.Specification.Operations.DiffPoint

@[expose] public section

/-!
# [1, Alg. 3 (exits)]: a GJK-style search for a separating or an intersecting direction

The two conclusive exits of `Alg. 3` (line 4-5 `safe`, line 12-13 `unsafe`), folded over a given
direction sequence `ℓ` and a fuel bound, since the loop need not terminate. The Gram-Schmidt
direction search (lines 18-25) and the `falsifiable`/`Δt`-halving restart (lines 7, 14-16) only
change which direction is tried, never whether an exit is sound, so they are not modelled. The
paper's `R̂(t)` (a `SupportBound`, line 4) and `R̲(t)` (a `SupportWitness`, line 10) are one bound
and one witness on the same `O`. Real-only, a specification: oracles over every direction, and the
soundness is the theorem.

## Inputs
* `bO` – bounds of the reachable set
* `bU` – bounds of the unsafe set
* `wO` – witnesses of the reachable set
* `wU` – witnesses of the unsafe set
* `ℓ` – sequence of directions
* `fuel` – number of directions tried

## Output
* safe, unsafe or undecided

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}
open scoped Classical


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [1, Alg. 3 (exits), l. 4-13] for one direction `ℓ i`: `safe` once the bounds
separate, `violated` once the accumulated hull reaches the origin, else the
new point is folded in. A reached answer is carried forward, extra fuel harmless. -/
noncomputable def aux_verifyConvexStep (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) :
    VerifyAnswer × Set α → ℕ → VerifyAnswer × Set α
  | (.safe, V), _ => (.safe, V)
  | (.violated, V), _ => (.violated, V)
  | (.undecided, V), i =>
      -- 4. `ρ(R̂(t), ℓᵢ) + ρ(L, −ℓᵢ)`, the upper bound against the unsafe set's support function
      let sep := (bO (ℓ i)).val + (bU (-(ℓ i))).val
      -- 5. `if … < 0 then return safe`
      if sep < 0 then (.safe, V)
      else
        -- 10. `v̌ᵢ ← ν(Ř(t), ℓᵢ) − ν(L, −ℓᵢ)`
        let v := diffPoint wO wU (ℓ i)
        -- 11. `P̌ ← conv(P̌, v̌ᵢ)`: the vertices are kept, the hull is taken at line 12
        let V' := insert v V
        -- 12. `if 0 ∈ P̌ then return unsafe`
        if (0 : α) ∈ convexHull ℝ V' then (.violated, V') else (.undecided, V')


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3 (exits)]: fold `aux_verifyConvexStep` over `fuel` directions drawn from
`ℓ`, starting undecided with nothing accumulated. -/
noncomputable def verifyConvex (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) (fuel : ℕ) :
    VerifyAnswer :=
  -- 1. `P̌ ← ∅` (and no answer yet)
  let init : VerifyAnswer × Set α := (.undecided, ∅)
  -- 2. `repeat`: lines 4-13 once per direction `ℓᵢ`, `fuel` times at most
  let final := (List.range fuel).foldl (aux_verifyConvexStep bO bU wO wU ℓ) init
  -- 5., 13. the answer a pass reached, `safe` or `unsafe`; `undecided` once `fuel` is spent
  final.1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
