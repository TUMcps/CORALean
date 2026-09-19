import CORALean.ContDynamics.LinearSys.MatExp.Enclosures

/-!
# The exponential remainder, entrywise

`E(Δt,η)` of [1]'s eq. (18), the subject of `Lemma 1`: the matrix
`e^{|A|Δt} − Σᵢ₌₀^η (|A|Δt)ⁱ/i!`, built from `A`'s entrywise absolute value
rather than bounded by a single scalar under an operator norm. It is a
*different* quantity from `expRemainderBound (Δt • A) η` — sharper, entry by
entry, and with no side condition of its own, since it is a plain difference of
two convergent series rather than a bound written as a ratio that can blow up.
[1]'s interval matrix `[−E(Δt,η), E(Δt,η)]` is this matrix read as a symmetric
radius, which converging to `0` trivializes, so nothing further is defined for
it here.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Inner- and Outer-Approximations of
      Reachable Sets". IEEE Transactions on Automatic Control, vol. 68, no. 12,
      2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The entrywise absolute value `|A|` of eq. (18) in [1]. -/
noncomputable def MatExp.absMat (A : Mat ℝ n n) : Mat ℝ n n := fun i j => |A i j|

/-- `E(Δt,η)` of eq. (18), the subject of [1, Lemma 1]: the matrix exponential's
Taylor remainder taken at `|A|` rather than at `A`, entrywise dominating the
true remainder. -/
noncomputable def MatExp.expRemainderMat (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) : Mat ℝ n n :=
  exp (Δt • MatExp.absMat A) - MatExp.expTaylor (Δt • MatExp.absMat A) η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
