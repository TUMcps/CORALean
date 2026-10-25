module

public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparation
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationSubset

@[expose] public section

/-!
# The input reach set separates exactly, not just up to enclosure

The separation of [1, Prop. 4] as it is printed: an equality. Both inclusions are available
(`inputReach_separation` concatenates two shorter runs into one over `[0, a+b]`,
`inputReach_separation_subset` takes an arbitrary such run apart) so `P_R(a+b)` is exactly
`e^{Ab} P_R(a) + P_R(b)`. At `a ∈ [0, r]` and `b = kr` it is [1, Prop. 4] at one time of the window
`[kr, (k+1)r]`, and the union over the window is the printed equation. `0 ≤ a` and `0 ≤ b` are what
make the windows windows, and a bounded input set is what makes every admissible input integrable,
so that the split at `a` and the concatenation at `a` are both legal.

## Inputs
* `sys` – linear system
* `U` – input set
* `a` – first window length
* `b` – second window length

## Hypotheses
* `ha` – first length nonnegative
* `hb` – second length nonnegative
* `hbdd` – input set bounded

## Conclusion
* the contribution of the joined window equals the propagated first plus the second

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 4] at every time of a window: the input reach set over a window is exactly
the first part's, propagated across the second, plus the second part's. -/
theorem LinearSys.inputReach_separation_eq (sys : LinearSys 𝕋 n) {U : S n} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbdd : Bornology.IsBounded (construct U)) :
    sys.inputReach U (a + b)
      = (fun y => exp (b • toRealMat sys.A) *ᵥ y) '' sys.inputReach U a
        + sys.inputReach U b :=
  Set.Subset.antisymm (sys.inputReach_separation_subset ha hb hbdd)
    (sys.inputReach_separation ha hb hbdd)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
