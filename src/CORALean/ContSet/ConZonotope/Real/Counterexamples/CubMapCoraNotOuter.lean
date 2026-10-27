module

public import CORALean.ContSet.ConZonotope.Real.Theorems.CubMapOuter
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import CORALean.Global.StepOf

@[expose] public section

/-!
# CORA's `conZonotope/cubMap` loses the constraint on a factor it does not see

`aux_cubMapSingle` rebuilds the constraint matrix from the *linear* monomials of the exponent matrix
of `polyZonotope/cubMap(...)`, which deletes every all-zero generator column
(`removeRedundantExponents`): a factor the cubic map does not depend on keeps no linear monomial,
its column of `A` stays zero, and `A β = b` is imposed on the others alone.
For `z = x₁² · x₁` and `c = (1, 0)`, `G = I`, `A = [1 1]`, `b = 0` the image is
`(1 + β₁)³ = [0, 8]`. CORA's polynomial zonotope keeps the linear monomial `β₁` alone, so
`A = [1 0 0]`, and `β₁²` moves half into the center, `c = 5/2`: the set `[0, 5]` misses `z = 8` at
`β₁ = 1` (read from the source, not run).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's cubic map misses a point of the exact image
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The constrained zonotope `c = (1, 0)`, `G = I`, `A = [1 1]`, `b = 0`. -/
@[step_of ConZonotope.cubMapCora_not_outer]
def ConZonotope.step_cubCexIn : ConZonotope (Vec ℝ 2) where
  h := 2
  c := ![1, 0]
  G := ![![1, 0], ![0, 1]]
  P := HPolytope.eqs (!![1, 1] : Mat ℝ 1 2) ![0]

/-- `z = x₁² · x₁`: `T{1,1} = diag(1, 0)`, `T{1,2} = 0`. -/
@[step_of ConZonotope.cubMapCora_not_outer]
def ConZonotope.step_cubCexTensor : Fin 1 → Fin 2 → Mat ℝ 2 2 :=
  fun _ k => if k = 0 then !![1, 0; 0, 0] else 0

/-- What `aux_cubMapSingle` returns for them, traced by hand: center `5/2`, generators
`(3, 3/2, 1)` and the constraint `γ₁ = 0` on the one linear monomial left. -/
@[step_of ConZonotope.cubMapCora_not_outer]
noncomputable def ConZonotope.step_cubCexCora : ConZonotope (Vec ℝ 1) where
  h := 3
  c := ![5 / 2]
  G := ![![3], ![3 / 2], ![1]]
  P := HPolytope.eqs (!![1, 0, 0] : Mat ℝ 1 3) ![0]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The point `β = (1, -1)` of the input, `x = (2, -1)`. -/
private theorem ConZonotope.aux_cubCex_mem : -- --- CONCL ---
    (![(2 : ℝ), -1] : Vec ℝ 2) ∈ ConZonotope.step_cubCexIn.construct := by -- --- PROOF ---
  refine ⟨![1, -1], ?_, ?_, ?_⟩
  -- both factors lie in `[-1, 1]`
  · intro j
    have : ∀ j : Fin 2, |(![1, -1] : Vec ℝ 2) j| ≤ 1 := fun j => by
      fin_cases j <;> simp
    exact this j
  -- and satisfy `β₁ + β₂ = 0`
  · refine HPolytope.mem_eqs_iff.mpr fun i => ?_
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  -- the point is `c + β₁ g₁ + β₂ g₂`
  · funext j
    have : ∀ j : Fin 2, (![2, -1] : Vec ℝ 2) j
        = (![1, 0] : Vec ℝ 2) j + ∑ k : Fin 2, (![1, -1] : Vec ℝ 2) k • (![![1, 0], ![0, 1]] :
          Fin 2 → Vec ℝ 2) k j := fun j => by
      fin_cases j <;> norm_num [Fin.sum_univ_two]
    exact this j

/-- The same point is in `ConZonotope.cubMap`, which keeps the linear generator of `β₂`. -/
private theorem ConZonotope.aux_cubMap_cex_mem :
    PolyZonotope.cubEval ConZonotope.step_cubCexTensor ![2, -1]
      ∈ (ConZonotope.step_cubCexIn.cubMap ConZonotope.step_cubCexTensor).construct :=
  ConZonotope.cubMap_outer _ _ ⟨![2, -1], ConZonotope.aux_cubCex_mem, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's result does not contain the cubic image `z = 8` of the point `x = (2, -1)`. -/
theorem ConZonotope.cubMapCora_not_outer : -- --- CONCL ---
    ∃ x ∈ ConZonotope.step_cubCexIn.construct,
      PolyZonotope.cubEval ConZonotope.step_cubCexTensor x
        ∉ ConZonotope.step_cubCexCora.construct := by -- --- PROOF ---
  refine ⟨![2, -1], ConZonotope.aux_cubCex_mem, ?_⟩
  -- the three coefficients, as a plain vector
  have key : ∀ γ : Vec ℝ 3, (∀ j, |γ j| ≤ 1)
      → γ ∈ (HPolytope.eqs (!![1, 0, 0] : Mat ℝ 1 3) ![0]).construct
      → PolyZonotope.cubEval ConZonotope.step_cubCexTensor ![2, -1]
        ≠ ![5 / 2] + ∑ j : Fin 3, γ j • (![![3], ![3 / 2], ![1]] : Fin 3 → Vec ℝ 1) j := by
    intro γ hγ hP hx
    -- the constraint pins the first coefficient to `0`
    have h0 : γ 0 = 0 := by
      have := HPolytope.mem_eqs_iff.mp hP 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    -- so the output coordinate is at most `5/2 + 3/2 + 1 = 5`, but the image point is `8`
    have h1 := congrFun hx 0
    have b1 := abs_le.mp (hγ 1)
    have b2 := abs_le.mp (hγ 2)
    simp [PolyZonotope.cubEval, ConZonotope.step_cubCexTensor, Fin.sum_univ_two,
      Fin.sum_univ_three, h0, dotProduct, Matrix.mulVec] at h1
    nlinarith [b1.1, b1.2, b2.1, b2.2]
  rintro ⟨γ, hγ, hP, hx⟩
  exact key γ hγ hP hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
