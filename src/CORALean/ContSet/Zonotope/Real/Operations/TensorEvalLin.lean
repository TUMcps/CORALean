module

public import CORALean.ContSet.Zonotope.Real.Operations.TensorEval
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `Zonotope.tensorEvalLin`

The tensor product at a fixed point `x` is linear in the tensor, which is what lets
`tensorMultiplication_zono` treat the center and the generators of a matrix zonotope of tensors one
by one.

## Inputs
* `x` – vector

## Output
* linear map evaluating a tensor at `x`
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `M ↦ Mᵢⱼₖₗ xⱼ xₖ xₗ`, linear in `M`. -/
noncomputable def Zonotope.tensorEvalLin (x : Vec ℝ n) :
    Tensor3 ℝ n →ₗ[ℝ] Vec ℝ n where
  toFun M := Zonotope.tensorEval M x
  map_add' M N := by
    funext d
    simp only [Zonotope.tensorEval, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    funext d
    simp only [Zonotope.tensorEval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun e _ => ?_
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
