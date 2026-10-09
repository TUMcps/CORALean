import CORALean.ContDynamics.LinearSys.MatExp.Operations.HalfSqBoundsFloat
import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.ContSet.Interval.Float.Operations.MulLo

/-!
# The second-order Taylor term, at one float matrix

`expW`: [1, Lemma 3.1]'s `W(t) = M t + ½ M² t²` at a stored matrix `M` and time `t`, as
`Real.MatExp.expW` has it, in the interval matrix it lies in. Neither the entries of `M²` (a dot
product) nor `½ t²` is held exactly by a float, so an entry is `t M_ij` plus the product of two
brackets, each rounded outward.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `W(t) = M t + ½ M² t²` at one matrix, as the interval matrix holding it. -/
def MatExp.expW (M : Mat 𝕋 n n) (t : 𝕋) : Interval (Mat 𝕋 n n) :=
  let ht := MatExp.halfSqBounds t                                   -- ½ t², bracketed
  ⟨fun i j => addDown (mulDown t (M i j))                           -- t M
      (Interval.mulLo ht.1 ht.2 (dotDown (M i) fun k => M k j) (dotUp (M i) fun k => M k j)),
    fun i j => addUp (mulUp t (M i j))
      (Interval.mulHi ht.1 ht.2 (dotDown (M i) fun k => M k j) (dotUp (M i) fun k => M k j))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
