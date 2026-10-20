module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.DependentTerms
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalW
public import CORALean.ContSet.Interval.Real.Operations.ExactSquare
public import CORALean.ContSet.Interval.Real.Operations.OfCenterRadius
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `MatExp.dependentTerms`

CORA's `@intervalMatrix/dependentTerms`, which computes the exact square and the exact second-order
Taylor terms in one loop. `sq` is `exactSquare`. `H` is the loop's `H` before the identity: entry
`(i, j)` is `A i j (r + ½ r² (A i i + A j j)) + ½ r² ∑_{k ≠ i, j} A i k A k j` off the diagonal, and
on it `∑_{k ≠ i} A i k A k i` plus the range `[g, κ]` of `a r + ½ a² r²` over `A i i`, with `g = -½`
when `-1/r` is in `A i i` and the smaller end value otherwise: this is `expIntervalW`
(Lemma 3.1 of the thesis), term for term. Both results are rebuilt as center and radius, as CORA
does.

## Inputs
* `A` – interval matrix
* `r` – step length

## Output
* squared and linear dependent terms of the interval matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[intSq, intH] = dependentTerms(obj, r)`. -/
noncomputable def MatExp.dependentTerms (A : Interval (Mat ℝ n n)) (r : ℝ) :
    MatExp.DependentTerms n :=
  let sq := Interval.exactSquare A
  let H := MatExp.expIntervalW A r
  { intSq := Interval.ofCenterRadius (r ^ 2 • sq.center) (r ^ 2 • sq.radius)
    intH := Interval.ofCenterRadius (H.center + 1) H.radius }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
