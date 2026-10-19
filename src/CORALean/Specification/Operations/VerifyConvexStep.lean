module

public import CORALean.Specification.Definitions.VerifyAnswer
public import CORALean.Specification.Operations.DiffPoint
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# [1, Alg. 3 (exits), l. 4-13]: one direction of the search

`verifyConvexStep`: `safe` once the bounds separate, `violated` once the accumulated hull
reaches the origin, else the new point is folded in. A reached answer is carried forward,
extra fuel harmless.

Real-only, a specification: it decides from bounds and witnesses supplied as oracles over every
direction, and its soundness is the theorem.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Classical

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3 (exits), l. 4-13] for one direction `ℓ i`: `safe` once the bounds
separate, `violated` once the accumulated hull reaches the origin, else the
new point is folded in. A reached answer is carried forward, extra fuel harmless. -/
noncomputable def verifyConvexStep (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
