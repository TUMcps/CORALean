module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermHi
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermLo
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# Interval matrices: the second-order Taylor term, exactly

`expIntervalW`: `W(t)` of [1, Prop. 4] as an interval matrix. `A` occurring twice in
`W(t) = A t + ½ A² t²` means ordinary interval arithmetic over-approximates it. Entry by entry it
rearranges into a *single-use expression* off the diagonal,
`W i j = A i j (t + ½ t² (A i i + A j j)) + ½ t² ∑_{k ≠ i, j} A i k A k j`, where interval
arithmetic is exact. On the diagonal `A i i` is left over in `γ(a) = a t + ½ a² t²`, so its
range over a box is `quadTermLo`/`quadTermHi`. CORA computes the same term in
`@intervalMatrix/dependentTerms.m`.

## Inputs
* `A` – interval matrix
* `t` – time

## Output
* interval matrix of the second-order Taylor term

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Sonnet 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `W(t)` of [1, Prop. 4] as an interval matrix: the single-use rearrangement
off the diagonal, the parabola's range on it, and the same `k ≠ i, j`
row-column sum under both. -/
noncomputable def MatExp.expIntervalW (A : Interval (Mat ℝ n n)) (t : ℝ) :
    Interval (Mat ℝ n n) where
  inf := fun i j =>
    (if i = j then MatExp.quadTermLo t (A.inf i i) (A.sup i i)
      else Interval.mulLo (A.inf i j) (A.sup i j)
        (t + t ^ 2 / 2 * (A.inf i i + A.inf j j)) (t + t ^ 2 / 2 * (A.sup i i + A.sup j j)))
    + t ^ 2 / 2 * ∑ k ∈ Finset.univ \ {i, j},
        Interval.mulLo (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)
  sup := fun i j =>
    (if i = j then MatExp.quadTermHi t (A.inf i i) (A.sup i i)
      else Interval.mulHi (A.inf i j) (A.sup i j)
        (t + t ^ 2 / 2 * (A.inf i i + A.inf j j)) (t + t ^ 2 / 2 * (A.sup i i + A.sup j j)))
    + t ^ 2 / 2 * ∑ k ∈ Finset.univ \ {i, j},
        Interval.mulHi (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
