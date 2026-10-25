module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.HalfSqBoundsFloat
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo

@[expose] public section

/-!
# The second-order Taylor term, at one float matrix

`expW`: [1, Prop. 4]'s `W(t) = M t + ½ M² t²` at a stored matrix `M` and time `t`, as
`Real.MatExp.expW` has it, in the interval matrix it lies in. Neither the entries of `M²` (a dot
product) nor `½ t²` is held exactly by a float, so an entry is `t M_ij` plus the product of two
brackets, each rounded outward.

## Inputs
* `M` – float matrix
* `t` – float time

## Output
* float interval matrix holding the second-order Taylor term

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `W(t) = M t + ½ M² t²` at one matrix, as the interval matrix holding it. -/
def MatExp.expW (M : Mat 𝕋 n n) (t : 𝕋) : Interval (Mat 𝕋 n n) :=
  let ht := MatExp.halfSqBounds t                                   -- ½ t², bracketed
  ⟨fun i j => addDown (mulDown t (M i j))                           -- t M
      (Interval.mulLo ht.inf ht.sup (dotDown (M i) fun k => M k j) (dotUp (M i) fun k => M k j)),
    fun i j => addUp (mulUp t (M i j))
      (Interval.mulHi ht.inf ht.sup (dotDown (M i) fun k => M k j) (dotUp (M i) fun k => M k j))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
