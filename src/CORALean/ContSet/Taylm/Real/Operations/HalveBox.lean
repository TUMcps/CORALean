import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic

/-!
# Halving a box

Lines 13-14 of [1, Alg. 1]: the first half of `[x]` along coordinate `β` keeps the lower end and
ends at the midpoint, `x̄_β - rad`; the rest is the second half, from the midpoint up.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.halveBox (B : Fin n → ℝ × ℝ) (β : Fin n) :
    (Fin n → ℝ × ℝ) × (Fin n → ℝ × ℝ) :=
  let m := ((B β).1 + (B β).2) / 2
  (Function.update B β ((B β).1, m), Function.update B β (m, (B β).2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
