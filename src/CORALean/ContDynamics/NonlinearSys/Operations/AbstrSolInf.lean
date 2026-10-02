import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The non-truncated set of abstraction errors

`[1, (32)]`: `R^∞_abs(h) = ⊕_{p≥0} h^{p+1}/(p+1)! · Aᵖ(h) Ψ(h)`, the set
`[1, (8)]` would compute if it never truncated the series and never paid a
remainder box for the tail; `[1, (31)]` measures the local abstraction error on
this instead, it being the quantity the gain function is about.

`A` and `Ψ` are functions of `h` and not a fixed matrix and set: both are read
off a linearization point that `[1, (6)]` puts half a step ahead, so shrinking
the step moves them — which is what makes `[1, Def. 5]`'s comparison of
`R^∞_abs(δh)` with `R^∞_abs(h)` a comparison of two expansions.

A `Set` and not a representation: an infinite Minkowski sum has no finite
generator matrix. Its points are the sums of the series whose `p`-th term comes
from the `p`-th summand, each `ψ p` chosen independently — the whole content of
`[1, Prop. 1]`, where the summands' row norms are added rather than the matrices
first. `HasSum` and not a limit of partial sums: `⊕` is commutative, so an
unordered family sums unconditionally, and over a bounded `Ψ h` both agree.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R^∞_abs(h)`: what `Σₚ h^{p+1}/(p+1)! · A(h)ᵖ ψₚ` sums to, over independent
choices `ψₚ ∈ Ψ(h)`. -/
noncomputable def abstrSolInf (A : ℝ → Mat ℝ n n) (Ψ : ℝ → Set (Vec ℝ n)) (h : ℝ) :
    Set (Vec ℝ n) :=
  {x | ∃ ψ : ℕ → Vec ℝ n, (∀ p, ψ p ∈ Ψ h) ∧
    HasSum (fun p => (h ^ (p + 1) / (Nat.factorial (p + 1) : ℝ)) • (A h ^ p *ᵥ ψ p)) x}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
