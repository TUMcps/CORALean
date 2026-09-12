import CORALean.ContSet.Interval.Real.Operations.MulHi
import CORALean.ContSet.Interval.Real.Operations.MulLo

/-!
# Interval matrices: the second-order Taylor term, exactly

[1, Lemma 3.1]. `W(t) = A t + ½ A² t²` has `A` occurring twice, so ordinary
interval arithmetic over-approximates it. Entry by entry it rearranges into a
*single-use expression* off the diagonal,
`W i j = A i j (t + ½ t² (A i i + A j j)) + ½ t² ∑_{k ≠ i, j} A i k A k j`,
where every variable occurs once and interval arithmetic is therefore exact.

On the diagonal the row-column sum is single-use too, but `A i i` is left over
in `γ(a) = a t + ½ a² t²`. `γ` is an upward parabola, so its range over a box
is `quadTermLo`/`quadTermHi`: `-1/2` at the vertex `-1/t` where the box
straddles it, an endpoint otherwise.

CORA computes the same term in `@intervalMatrix/dependentTerms.m`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- The `γ` of [1, Lemma 3.1]: what a diagonal entry contributes through itself,
and the one place a variable occurs twice. -/
noncomputable def MatExp.quadTerm (t a : ℝ) : ℝ := a * t + a ^ 2 * t ^ 2 / 2

/-- The least value `quadTerm t` takes on `[a, b]`. `-1/t` is the vertex; where
`t = 0` the `if` reads `-1/t` as `0` and this is sound but not tight. -/
noncomputable def MatExp.quadTermLo (t a b : ℝ) : ℝ :=
  if a ≤ -1 / t ∧ -1 / t ≤ b then -(1 / 2)
  else min (MatExp.quadTerm t a) (MatExp.quadTerm t b)

/-- The greatest, always at an endpoint: the parabola opens upwards. -/
noncomputable def MatExp.quadTermHi (t a b : ℝ) : ℝ :=
  max (MatExp.quadTerm t a) (MatExp.quadTerm t b)

/-- `W(t) = M t + ½ M² t²` at one matrix, which is orders one and two of
`expTaylor (t • M)`. -/
noncomputable def MatExp.expW (M : Mat ℝ n n) (t : ℝ) : Mat ℝ n n :=
  t • M + (t ^ 2 / 2) • (M * M)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `W(t)` of [1, Lemma 3.1] as an interval matrix: the single-use rearrangement
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
