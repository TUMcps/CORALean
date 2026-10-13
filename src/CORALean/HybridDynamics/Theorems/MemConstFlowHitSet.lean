module

public import CORALean.HybridDynamics.Definitions.ConstFlowHitSet
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A guard hit within `E` of the constant flow lies in eq. (1)'s set

[1, Eq. 1], by its derivation: a state `x₀ + bt + e` with `e ∈ E` that lies on
`nᵀx = d` has `t = (d - nᵀx₀ - nᵀe)/(nᵀb)`; inserting `t` gives
`(Cx₀ + w) + (-bnᵀ/(nᵀb)) e + e`, which the set holds, `e` entering both summands.
The set is larger than the hits, each summand drawing its own `e`, which costs only
tightness. `nᵀb ≠ 0` is what the division asks: a flow parallel to the guard never hits it.

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 1]: a state `x₀ + bt + e` on `nᵀx = d`, `e ∈ E`, lies in
`(Cx₀ + w) ⊕ (-bnᵀ/(nᵀb) ⊗ E) ⊕ E`. -/
theorem GuardMap.mem_constFlowHitSet {x₀ b nv : Vec ℝ n} {d t : ℝ} {E : Set (Vec ℝ n)}
    {e : Vec ℝ n} (hb : nv ⬝ᵥ b ≠ 0) (he : e ∈ E) (hhit : nv ⬝ᵥ (x₀ + t • b + e) = d) :
    x₀ + t • b + e ∈ GuardMap.constFlowHitSet x₀ b nv d E := by -- --- PROOF ---
  -- the hitting time, read off the hyperplane
  have ht : t = (d - nv ⬝ᵥ x₀ - nv ⬝ᵥ e) / (nv ⬝ᵥ b) := by
    rw [eq_div_iff hb, ← hhit]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  simp only [GuardMap.constFlowHitSet]
  refine ⟨_, ⟨_, rfl, _, ⟨e, he, rfl⟩, rfl⟩, e, he, ?_⟩
  -- `(Cx₀ + w) + Me = x₀ + ((d - nᵀx₀ - nᵀe)/(nᵀb)) b`, coordinate by coordinate
  ext i
  simp only [Pi.add_apply, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.neg_mulVec, vecMulVec_mulVec, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  rw [ht]
  field_simp
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
