module

public import CORALean.ContDynamics.LinearSys.Operations.VerifySearchLoop

@[expose] public section

/-!
# [1, Alg. 3 (search)]: from line 1

Line 1 of `[1, Alg. 3 (search)]` — `i ← 1`, `ℓ₁ ← I_n(·,1)`, `Δt ← t`, `P̂, P̌ ← ∅`,
`falsifiable ← true` — and then the loop of `verifySearchLoop`. `ℓ₁` is the first coordinate
functional, written as a sum over the coordinates so that dimension `0` needs no case; `k = 1`
because `Δt = t`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, Recenter (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3 (search)]: the answer of the first exit the search reaches within `fuel`
iterations from `X₀`, `U` and the time `t`, `undecided` if there is none. -/
noncomputable def LinearSys.verifySearch (sys : LinearSys 𝕋 n) (X₀ U : S n) (t : ℝ) (η : ℕ)
    (ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ) (ν₀ νU νL : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n)
    (νhat : ℝ → (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n) (ρL : (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ)
    (inHull : List (Vec ℝ n) → Bool)
    (closestFacet : List (Vec ℝ n) → (Vec ℝ n →ₗ[ℝ] ℝ) × List ℕ)
    (gramSchmidt : List (Vec ℝ n) → (Vec ℝ n →ₗ[ℝ] ℝ)) (fuel : ℕ) : VerifyAnswer :=
  -- 1. i ← 1
  let i : ℕ := 1
  -- 1. ℓ₁ ← I_n(·,1)
  let ℓ₁ : Vec ℝ n →ₗ[ℝ] ℝ := ∑ j : Fin n, if (j : ℕ) = 0 then LinearMap.proj j else 0
  -- 1. Δt ← t
  let Δt := t
  -- 1. P̂ ← ∅
  let Phat : List (Vec ℝ n) := []
  -- 1. P̌ ← ∅
  let Pcheck : List (Vec ℝ n) := []
  -- 1. falsifiable ← true
  let falsifiable := true
  -- 2. repeat
  sys.verifySearchLoop X₀ U η ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt ℓ₁ fuel
    ⟨i, ℓ₁, Δt, 1, Phat, Pcheck, falsifiable⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
