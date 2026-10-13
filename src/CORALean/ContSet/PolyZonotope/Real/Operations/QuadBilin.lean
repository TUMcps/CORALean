module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.BilinearMap

@[expose] public section

/-!
# The quadratic form family, bundled as a bilinear map

`(x, y) ↦ (xᵀQ₁y, …, xᵀQₘy)`, which is bilinear because a dot product is linear
in either vector and `mulVec` is linear in the one it moves. `PolyZonotope.bilin`
at it is `quadMapDep`, so the exponent and generator bookkeeping of a pairing
over shared factors is written once and specialised here rather than repeated.

Bundled as `→ₗ →ₗ` and not left as a function with four side conditions,
because that is the only form `bilin` takes: nothing about `Q` is ever used
beyond bilinearity. `quadEval` is this at a repeated argument, definitionally,
which is what lets `quadMapDep_exact` read off `bilin_exact` with no step in
between.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The quadratic form family as a bilinear map, one matrix per output
coordinate; `bilin` at it is `quadMap`. -/
def PolyZonotope.quadBilin (Q : Fin m → Mat ℝ n n) :
    Vec ℝ n →ₗ[ℝ] Vec ℝ n →ₗ[ℝ] Vec ℝ m :=
  LinearMap.mk₂ ℝ (fun (x y : Vec ℝ n) (k : Fin m) => x ⬝ᵥ (Q k *ᵥ y))
    (fun _ _ _ => funext fun _ => add_dotProduct _ _ _)
    (fun _ _ _ => funext fun _ => smul_dotProduct _ _ _)
    (fun _ _ _ => funext fun _ => by rw [Pi.add_apply, mulVec_add, dotProduct_add])
    (fun _ _ _ => funext fun _ => by rw [Pi.smul_apply, mulVec_smul, dotProduct_smul])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
