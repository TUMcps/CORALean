module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Robust positively invariant sets

[1, Sec. 3.1.2], after Blanchini: `S` is invariant if every solution from a state of `S`
stays in `S` at every `t > 0` for every admissible input,
`∀ t > 0, ∀ u(·) ∈ U(·), ∀ [x(0); y(0)] ∈ S : γ(t, x(0), y(0), u(·)) ∈ S`, where `γ` is the
unique solution [1, Sec. 3.1] assumes for every consistent initial state and input. `γ` is
an argument here, as in the paper; a state `x` stands for the pair `[x; y]` of differential
and algebraic variables, and `U` for the admissible input signals `U(·)`.

## Inputs
* `γ` – solution map of the system
* `U` – set of admissible input signals
* `S` – candidate invariant set

## Output
* the proposition that no admissible input drives a solution out of the set

## References

* [1] [M. Althoff. "Benchmarks for the Formal Verification of Power Systems". Proceedings of 9th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH22),
      2022.](../../../references/2022/althoff-arch-power-systems.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X Inp : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3.1.2]: no admissible input drives a solution from `S` out of it. -/
def IsRobustInvariant (γ : ℝ → X → (ℝ → Inp) → X) (U : Set (ℝ → Inp)) (S : Set X) : Prop :=
  ∀ t > 0, ∀ u ∈ U, ∀ x₀ ∈ S, γ t x₀ u ∈ S

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
