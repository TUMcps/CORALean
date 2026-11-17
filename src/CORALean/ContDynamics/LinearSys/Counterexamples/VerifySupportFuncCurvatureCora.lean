module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `LinearSys.verifySupportFuncCurvatureCora`: the curvature distance of `priv_verifyRA_supportFunc`

CORA's `@linearSys/private/priv_verifyRA_supportFunc.m` bounds the support function of the
curvature set `C = F X₀` (the interval matrix `F = [F_c ± F_r]`, `X₀ = ⟨c, G⟩`) along `ℓ` by
`ℓ'(F_c c) + Σ|ℓ'(F_c G)| + |ℓ'(F_r Σ|[c G]|)|` (`dist.Cbloat`, ll. 257-258 and 388-390). The
comment there says the last term "requires diag(.)": `F_r Σ|[c G]|` is the radius `v` of a box
centered at the origin, whose support along `ℓ` is `|ℓ|'v`. CORA takes `|ℓ'v|`, which is smaller
whenever the signs of `ℓ` differ on the box. Modelled in `ℝ²` with no generators. Read from the
source, not run.

# CORA's curvature distance lies below the support of the curvature set

`F_c = 0`, `F_r = I`, `X₀ = {(1, 1)}`, `ℓ = (1, -1)`: `v = (1, 1)` and CORA's distance is
`|1 - 1| = 0`, while `M = diag(1, -1)` lies in `F` and `ℓ'(M c) = 2`. So the time-interval bound
of the step, which adds this distance, can stay below a value the set reaches.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's curvature distance is below the value of a point of `F X₀`
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- The model: CORA's code as printed, kept only to be refuted.
/-- `dist.Cbloat` for `X₀ = {c}`: `ℓ'(F_c c) + |ℓ'(F_r |c|)|` (ll. 257-258, no generators). -/
def LinearSys.verifySupportFuncCurvatureCora (ℓ c : Fin 2 → ℝ) (Fc Fr : Matrix (Fin 2) (Fin 2) ℝ) :
    ℝ :=
  let cx := Fc *ᵥ c                                               -- cx_Cbloat = intmatF.center*c_X0
  let G2x := Fr *ᵥ (fun i => |c i|)                               -- intmatF.rad*sum(abs(c_X0))
  ℓ ⬝ᵥ cx + |ℓ ⬝ᵥ G2x|                                           -- l'*cx + abs(l'*G2x)


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's distance is `0`; `diag(1, -1) ∈ [0 ± I]` maps `c = (1, 1)` to a point of value `2`. -/
theorem LinearSys.verifySupportFuncCurvatureCora_counterexample : -- --- CONCL ---
    LinearSys.verifySupportFuncCurvatureCora ![(1 : ℝ), -1] ![(1 : ℝ), 1] 0 1 = 0 ∧
      ∃ M : Matrix (Fin 2) (Fin 2) ℝ, (∀ i j, |M i j - (0 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤
        (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) ∧
      ![(1 : ℝ), -1] ⬝ᵥ (M *ᵥ ![(1 : ℝ), 1]) = 2 := by -- --- PROOF ---
  refine ⟨?_, !![1, 0; 0, -1], ?_, ?_⟩
  · simp [LinearSys.verifySupportFuncCurvatureCora, dotProduct, mulVec, Fin.sum_univ_two]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp
  · simp [dotProduct, mulVec, Fin.sum_univ_two, one_add_one_eq_two]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
