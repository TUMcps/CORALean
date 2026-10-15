module

public import CORALean.ContDynamics.LinParamSysDT.Operations.InputSet

@[expose] public section

/-!
# The combined input of a step lies in `inputSet`

A value `B u + c`, `B` from `sys.B` and `u` from `U`, lies in `sys.inputSet U`: the step's input in
state coordinates, as `LinParamSys.mem_inputSet` has it. With `IsTrajectory.canonical` this puts
every run into the canonical form at CORA's `V = B*U + c`.
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
theorem LinParamSysDT.mem_inputSet (sys : LinParamSysDT 𝕄 n) {U : S sys.m} {B : Mat ℝ n sys.m}
    (hB : B ∈ construct sys.B) {v : Vec ℝ sys.m} (hv : v ∈ construct U) :
    B *ᵥ v + sys.c ∈ construct (sys.inputSet U) :=
  Plus.plus_outer _ _ (Set.add_mem_add
    (Mtimes.mtimes_outer sys.B U (Set.mem_biUnion hB ⟨v, hv, rfl⟩))
    (OfPoint.mem_ofPoint sys.c))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
