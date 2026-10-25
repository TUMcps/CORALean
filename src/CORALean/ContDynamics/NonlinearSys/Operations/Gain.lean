module

public import CORALean.ContDynamics.NonlinearSys.Operations.GainDim

@[expose] public section

/-!
# The gain function

`[1, Def. 5]`: `φ(h;δ) = maxᵢ φᵢ(h;δ)`, the worst dimension's gain, which is
what `[1, Alg. 2]` tunes the time step size against. The maximum and not an
average: a step size is good enough only if every dimension's error shrinks
with it.

`⨆` rather than a `Finset.max'`, so that no nonemptiness proof has to be carried
through; in `n = 0` dimensions it is `sSup ∅ = 0`, junk of the same kind
`boxDiameter` returns off its domain and for the same reason.

## Inputs
* `A` – matrix as a function of the step
* `Ψ` – error set as a function of the step
* `h` – step size
* `δ` – shrink factor

## Output
* the largest share of its width any dimension keeps

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `φ(h;δ)`: the largest share of its width any dimension of the error set
keeps when the time span shrinks from `h` to `δh`. -/
noncomputable def gain (A : ℝ → Mat ℝ n n) (Ψ : ℝ → Set (Vec ℝ n)) (h δ : ℝ) : ℝ :=
  ⨆ i, gainDim A Ψ h δ i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
