module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

/-!
# The non-truncated set of abstraction errors

`[1, (32)]`: `R^∞_abs(h) = ⊕_{p≥0} h^{p+1}/(p+1)! · Aᵖ(h) Ψ(h)`, the set `[1, (8)]` would compute
if it never truncated the series and never paid a remainder box for the tail; `[1, (31)]`
measures the local abstraction error on this instead. `A` and `Ψ` are functions of `h` and not a
fixed matrix and set: both are read off a linearization point that `[1, (6)]` puts half a step
ahead, so shrinking the step moves them (`[1, Def. 5]`). A `Set` and not a representation: an
infinite Minkowski sum has no finite generator matrix. Its points are the series sums whose `p`-th
term comes from the `p`-th summand, each `ψ p` chosen independently: `[1, Prop. 1]`.
`HasSum` and not a limit of partial sums: `⊕` is commutative, so a family sums unconditionally.

## Inputs
* `A` – matrix as a function of the step
* `Ψ` – error set as a function of the step
* `h` – step size

## Output
* the sums of the series over independent choices

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
