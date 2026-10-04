import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Linarith

/-!
# The radius condition of the LPV estimator has no solution

Eq. 20 of [1, Thm. 2] asks for `P = Pᵀ ≻ 0` and `γ > 0` with `[I ⋆; γP P] ≼ 0`. No `P` and `γ`
satisfy it, in any dimension `n ≥ 1`: the form at `(e_i, 0)` is the top-left entry of `I`,
`1 > 0`. So [1, Thm. 2] as printed holds vacuously. Its proof derives Eq. 20 from
`I - γ²P ≼ 0` (its Eq. 26) by a Schur complement, which is the condition the theorem needs.
CORA's `PRad-D` gain (`priv_observe_gain_PRadD`) imposes Eq. 20 as printed, `SM2 <= 0` with
`SM2 = [eye(n) ⋆; γP P]`, so every step of its bisection on `γ` is infeasible.

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      64(5):2092-2099, 2019.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.radiusLmi_infeasible (P : Mat ℝ n n) (γ : ℝ) (i : Fin n) :
    ¬ (-(fromBlocks (1 : Mat ℝ n n) (γ • P)ᵀ (γ • P) P)).PosSemidef := by -- --- PROOF ---
  intro h
  -- the form at `(e_i, 0)` is `-1`
  have hx := (posSemidef_iff_dotProduct_mulVec.mp h).2 (Sum.elim (Pi.single i 1) 0)
  simp only [star_trivial, neg_mulVec, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    mulVec_zero, add_zero, one_mulVec, dotProduct_neg, sumElim_dotProduct_sumElim,
    Pi.single_apply, dotProduct_single, mul_one, zero_dotProduct, if_true] at hx
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
