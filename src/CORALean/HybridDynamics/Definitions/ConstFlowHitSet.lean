module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# The set eq. (1) of [1] puts a guard hit in

[1, Eq. 1]: under constant flow `ż = b` from `x₀`, the hyperplane `nᵀz = d` is hit at
`z_h = Cx₀ + w`, `C = I - bnᵀ/(nᵀb)`, `w = bd/(nᵀb)`; a linear system's state, within
`E` of that flow, hits it inside `(Cx₀ + w) ⊕ (-bnᵀ/(nᵀb) ⊗ E) ⊕ E`. One `let` per
printed symbol; `-bnᵀ/(nᵀb) ⊗ E` is the set-based multiplication of a matrix and a set.

A set, as eq. (1) has it, not a representation: [1] computes with zonotopes only from
Sec. 5 on, where the state-dependent flow replaces `b`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 1]: `(Cx₀ + w) ⊕ (-bnᵀ/(nᵀb) ⊗ E) ⊕ E`, the guard hits from `x₀` within `E` of
the constant flow `b`. -/
def GuardMap.constFlowHitSet (x₀ b nv : Vec ℝ n) (d : ℝ) (E : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  let C : Mat ℝ n n := 1 - (nv ⬝ᵥ b)⁻¹ • vecMulVec b nv    -- `I - bnᵀ/(nᵀb)`
  let w : Vec ℝ n := (d / (nv ⬝ᵥ b)) • b                     -- `bd/(nᵀb)`
  let M : Mat ℝ n n := -((nv ⬝ᵥ b)⁻¹ • vecMulVec b nv)       -- `-bnᵀ/(nᵀb)`
  {C *ᵥ x₀ + w} + (M *ᵥ ·) '' E + E

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
