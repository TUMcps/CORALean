module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.HalfSqBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermHiFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermLoFloat

@[expose] public section

/-!
# Interval matrices: the second-order Taylor term, exactly, over a floating-point scalar

`expIntervalW`: `Real.MatExp.expIntervalW` rounded. The single-use rearrangement of
[1, Prop. 4] off the diagonal, `quadTermLo`/`quadTermHi` on it, and the `k ≠ i, j`
row-column sum under both. Every bound the exact layer takes at a real is taken at a bracket
here: `½ t²` by `halfSqBounds`, the factor by directed sums, the sum by `sumDown`/`sumUp` of
the corner hulls, and each product by the hull of its brackets. Each rounds away from the
interval, `inf` down and `sup` up.

## Inputs
* `A` – float interval matrix
* `t` – float time

## Output
* float interval matrix of the second-order Taylor term

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The entry `(i, j)` of `W(t)`'s interval, as an interval of floats. -/
def aux_expIntervalWEntry (A : Interval (Mat 𝕋 n n)) (t : 𝕋) (i j : Fin n) : Interval 𝕋 :=
  let ht := MatExp.halfSqBounds t                                   -- ½ t², bracketed
  let sLo := addDown (A.inf i i) (A.inf j j)                        -- A i i + A j j
  let sHi := addUp (A.sup i i) (A.sup j j)
  let fLo := addDown t (Interval.mulLo ht.inf ht.sup sLo sHi)           -- t + ½ t² (A i i + A j j)
  let fHi := addUp t (Interval.mulHi ht.inf ht.sup sLo sHi)
  let SLo := sumDown fun k => if k = i ∨ k = j then zero          -- ∑_{k ≠ i, j} A i k A k j
    else Interval.mulLo (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)
  let SHi := sumUp fun k => if k = i ∨ k = j then zero
    else Interval.mulHi (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)
  ⟨addDown (if i = j then MatExp.quadTermLo t (A.inf i i) (A.sup i i)
      else Interval.mulLo (A.inf i j) (A.sup i j) fLo fHi)
    (Interval.mulLo ht.inf ht.sup SLo SHi),
   addUp (if i = j then MatExp.quadTermHi t (A.inf i i) (A.sup i i)
      else Interval.mulHi (A.inf i j) (A.sup i j) fLo fHi)
    (Interval.mulHi ht.inf ht.sup SLo SHi)⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `W(t)` of [1, Prop. 4] as an interval matrix, rounded outward. -/
def MatExp.expIntervalW (A : Interval (Mat 𝕋 n n)) (t : 𝕋) : Interval (Mat 𝕋 n n) :=
  ⟨fun i j => (aux_expIntervalWEntry A t i j).inf, fun i j => (aux_expIntervalWEntry A t i j).sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
