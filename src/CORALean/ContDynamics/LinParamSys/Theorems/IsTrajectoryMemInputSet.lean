module

public import CORALean.ContDynamics.LinParamSys.Operations.InputSet

@[expose] public section

/-!
# The combined input of a run lies in `inputSet`

Every value `B t u t + c` of a run, `B t` drawn from `sys.B` and `u t` from `U`, lies in
`sys.inputSet U`, whether `B` is drawn afresh at every instant (`'varParam'`) or once
(`'constParam'`). With `IsTrajectory.canonical` this puts every run into the canonical form at
CORA's `V = B*U + c`.

## Inputs
* `sys` – system
* `U` – input set
* `B` – input matrix member
* `v` – input value

## Hypotheses
* `hB` – `B` lies in the input matrix set
* `hv` – `v` lies in `U`

## Conclusion
* the combined input lies in the input set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
  [Mtimes 𝕄 S] [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A matrix of `B` times a vector of `U`, plus `c`, is in `B U ⊕ c`. -/
theorem LinParamSys.mem_inputSet (sys : LinParamSys 𝕄 n) {U : S sys.m} {B : Mat ℝ n sys.m}
    (hB : B ∈ construct sys.B) {v : Vec ℝ sys.m} (hv : v ∈ construct U) :
    B *ᵥ v + sys.c ∈ construct (sys.inputSet U) :=
  Plus.plus_outer _ _ (Set.add_mem_add
    (Mtimes.mtimes_outer sys.B U (Set.mem_biUnion hB ⟨v, hv, rfl⟩))
    (OfPoint.mem_ofPoint sys.c))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
