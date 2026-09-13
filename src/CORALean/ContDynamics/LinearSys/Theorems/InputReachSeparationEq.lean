import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparation
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationSubset

/-!
# The input reach set separates exactly, not just up to enclosure

[1, Prop. 3.2] as it is printed: an equality. Both inclusions are available —
`inputReach_separation` concatenates two shorter runs into one over `[0, a+b]`,
`inputReach_separation_subset` takes an arbitrary such run apart — so
`P_R(a+b)` is exactly `e^{Ab} P_R(a) + P_R(b)`, and this is the antisymmetry.

Taking `a = (k-1)r + Δt` and `b = r` is the recursion [1, Prop. 3.2] states;
`k = 1`, so that `a = Δt`, is [1, Cor. 3.1].

`0 ≤ a` and `0 ≤ b` are what make the windows windows, and a bounded input set
is what makes every admissible input integrable, so that the split at `a` and
the concatenation at `a` are both legal.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3.2], and at `a = Δt`, `b = r` its [1, Cor. 3.1]: the input reach
set over a window is exactly the first part's, propagated across the second,
plus the second part's. -/
theorem LinearSys.inputReach_separation_eq (sys : LinearSys 𝕋 n) {U : S n} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbdd : Bornology.IsBounded (construct U)) :
    sys.inputReach U (a + b)
      = (fun y => exp (b • toRealMat sys.A) *ᵥ y) '' sys.inputReach U a
        + sys.inputReach U b :=
  Set.Subset.antisymm (sys.inputReach_separation_subset ha hb hbdd)
    (sys.inputReach_separation ha hb hbdd)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
