module

public import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A specification checked on the output set holds of the output

What an output equation is added for: until there is one, a requirement can only be written
about the state, and a system whose safety is a property of what it *emits* has no way to say
so. This is `outputSet_outer` handed to `Specification.holds_of_outer`, the same step
`LinearSysDT.holds_of_reach` and `NeuralNetwork.holds_of_enclose` take. The specification lives
at the output dimension `r`, not at `n`: `C` is where the two come apart, and it is not
invertible in the cases that motivate an output, such as a projection onto measured coordinates.

## Inputs
* `out` – output equation
* `R` – state set
* `U` – input set
* `spec` – specification
* `x` – state
* `u` – admissible input

## Hypotheses
* `hx` – state in state set
* `hu` – input in input set
* `h` – specification holds on the output set

## Conclusion
* the specification holds on the output
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfScalarPoint 𝕋 S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ r)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OutputEq.holds_of_outputSet (out : OutputEq 𝕋 n m r) (R : S n) (U : S m)
    (spec : Specification ContSet) {x : Vec ℝ n} {u : Vec ℝ m}
    (hx : x ∈ construct R) (hu : u ∈ construct U)
    (h : spec.Holds (construct (out.outputSet R U))) : spec.Holds {out.eval x u} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (out.outputSet_outer R U hx hu)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
