import CORALean.ContSet.Taylm.Real.Taylm
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A term list evaluates to a continuous function

A sum of coefficients times products of coordinate powers.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.continuous_polyOf (L : List (ℝ × (Fin n → ℕ))) :
    Continuous fun t : Vec ℝ n => Taylm.polyOf L t := by -- --- PROOF ---
  induction L with
  | nil => simp only [Taylm.polyOf_nil]; exact continuous_const
  | cons a L ih =>
    simp only [Taylm.polyOf_cons]
    refine Continuous.add (continuous_const.mul ?_) ih
    unfold Taylm.monomial
    exact continuous_finsetProd _ fun k _ => (continuous_apply k).pow _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
