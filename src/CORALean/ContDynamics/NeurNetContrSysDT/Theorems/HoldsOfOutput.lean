module

public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.OutputOuter
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A specification checked on the output set holds along every run

`LinearSysDT.holds_of_output`'s statement, at the enclosed input set
`output_outer` reads the output at: `holds_of_reach` for the output rather
than the state, and for the same reason there — `C` in general not invertible.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
    [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.holds_of_output (sys : NeurNetContrSysDT 𝕋 S n)
    {Y : Type} [CORALean.ContSet Y (Vec ℝ sys.plant.q)]
    {o : ℕ} (ho : 0 < o) (R₀ : S n) (spec : Specification Y)
    {π : Vec ℝ n → Vec ℝ sys.plant.m} (hπ : sys.contr.Sound π)
    {x : ℕ → Vec ℝ n} (traj : sys.Trajectory π R₀ x) (k : ℕ)
    (h : spec.Holds (construct (sys.plant.outputEq.outputSet (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩)
      (sys.contr.enclose (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩))))) :
    spec.Holds {sys.plant.outputEq.eval (x k) (π (x k))} :=
  spec.holds_of_outer
    (Set.singleton_subset_iff.mpr (sys.output_outer ho R₀ hπ traj k)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
