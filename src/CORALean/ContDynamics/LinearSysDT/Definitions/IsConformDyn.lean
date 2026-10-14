module

public import CORALean.ContDynamics.LinearSysDT.Operations.ConformReach
public import CORALean.ContDynamics.LinearSysDT.Operations.NominalState
public import CORALean.ContDynamics.LinearSysDT.Operations.Basic

@[expose] public section

/-!
# What the dynamic conformance check asks

`isconform_dyn` for a finite horizon [1]: every deviation `y_a(k) = y(k) - y*(k)` of a test
case's measured output from the nominal one, at every sample `k ≤ K`, lies in the deviation set
`R_k` of the conformance check, `N{k} y_a ≤ d{k}` for `polytope(R_k) = ⟨N, d⟩`. Prop-valued, as
`Isequal`. A check on the outputs one sample at a time: no claim that one run explains the
whole test case. One index `ι` for the pairs (test, sample), each with its own initial state
(CORA takes the one of the first sample of a test, `x(:,1,1)`).

## References

* [1] `contDynamics/@linearSysDT/isconform_dyn.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes

variable {n : ℕ} {ι : Type}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `res = ~numFailed`, over the samples `k ≤ K`. -/
def LinearSysDT.IsConformDyn (sys : LinearSysDT ℝ n) (X₀ : S n) (W : S sys.r) (V : S sys.s)
    (K : ℕ) (x0 : ι → Vec ℝ n) (u : ι → ℕ → Vec ℝ sys.m) (y : ι → ℕ → Vec ℝ sys.q) : Prop :=
  ∀ i, ∀ k, k ≤ K →
    y i k - sys.outputEq.eval (sys.nominalState (x0 i) (u i) k) (u i k)
      ∈ construct (sys.conformReach X₀ W V k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
