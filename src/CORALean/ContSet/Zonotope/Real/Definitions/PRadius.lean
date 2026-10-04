import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The P-radius of a zonotope

[1, Sec. 2]: `L = max_{z ∈ Z} ‖z - p‖²_P` for `P = Pᵀ ≻ 0`, the largest squared `P`-distance of a
point of `Z = p ⊕ H Bᵐ` from its centre. Written as the supremum; a zonotope is
compact, so it is attained. `P` is any matrix here: what is proved about it says which `P` it
needs.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `max_{z ∈ Z} (z - p)ᵀ P (z - p)`. -/
noncomputable def Zonotope.pRadius (P : Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) : ℝ :=
  sSup ((fun z => (z - Z.c) ⬝ᵥ (P *ᵥ (z - Z.c))) '' Z.construct)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
