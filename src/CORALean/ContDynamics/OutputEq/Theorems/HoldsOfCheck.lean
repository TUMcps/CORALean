module

public import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter
public import CORALean.Specification.Theorems.HoldsOfOuter
public import CORALean.Specification.Theorems.CheckSound

@[expose] public section

/-!
# A passed check on the output set holds of every output

`aux_holds_of_outputSet` with its hypothesis discharged by running `Specification.check` on
the set `outputSet` computed: a `true`, found by evaluation, is the specification on the
exact output of every state and input the two sets hold.

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

## Conclusion
* a passed check gives the specification on the output
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfScalarPoint 𝕋 S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ r)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A specification checked on the output set holds of the output. -/
private theorem OutputEq.aux_holds_of_outputSet (out : OutputEq 𝕋 n m r) (R : S n) (U : S m)
    (spec : Specification ContSet) {x : Vec ℝ n} {u : Vec ℝ m}
    (hx : x ∈ construct R) (hu : u ∈ construct U)
    (h : spec.Holds (construct (out.outputSet R U))) : spec.Holds {out.eval x u} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (out.outputSet_outer R U hx hu)) h


-- =======================================  MAIN THEOREM  ======================================= --

theorem OutputEq.holds_of_check [Contains ContSet (S r)] [IsDisjoint ContSet (S r)]
    (out : OutputEq 𝕋 n m r) (R : S n) (U : S m) (spec : Specification ContSet)
    {x : Vec ℝ n} {u : Vec ℝ m} (hx : x ∈ construct R) (hu : u ∈ construct U) :
    spec.check (out.outputSet R U) → (spec.Holds {out.eval x u}) :=
  fun h => out.aux_holds_of_outputSet R U spec hx hu (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
