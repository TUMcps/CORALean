module

public import CORALean.ContDynamics.NonlinearSys.Definitions.AdaptState

@[expose] public section

/-!
# `Alg. 2`'s loop state before the first step

`adaptInit`: the state [1, Alg. 2] needs before its first step, which [1]
describes for `k = 1` in prose rather than in the algorithm.

## Inputs
* `T` – time type
* `τ` – step size type
* `X₀` – start set
* `h₀` – initial horizon
* `φ₀` – initial gain
* `rabs₀` – initial abstraction radius
* `κ₀` – initial order

## Output
* the adaptive loop state before the first step

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}
variable {S : ℕ → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The state the adaptive step of [1] needs before its first step, which [1] describes for
`k = 1` in prose rather than in the algorithm. -/
def NonlinearSys.adaptInit {T τ : Type} [Zero T] (X₀ : S n) (h₀ φ₀ rabs₀ : τ) (κ₀ : ℕ) :
    NonlinearSys.AdaptState S n T τ :=
  { t := 0, R := X₀, Rτ := X₀, h := h₀, φ := φ₀, κ := κ₀, rabs := rabs₀ }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
