import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.OutputOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A specification checked on the output set holds along every run

`LinearSysDT.holds_of_output`'s statement, at the enclosed input set
`output_outer` reads the output at: `holds_of_reach` for the output rather
than the state, and for the same reason there — `C` in general not invertible.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.holds_of_output (sys : NeurNetContrSysDT 𝕋 S n)
    (out : OutputEq 𝕋 n n r) (o : ℕ) (R₀ : S n) (spec : Specification (Vec ℝ r))
    {x : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ x) (k : ℕ)
    (h : spec.Holds (construct (out.outputSet (sys.reach o R₀ k)
      (sys.contr.enclose (sys.reach o R₀ k))))) :
    spec.Holds {out.eval (x k) (sys.contr.eval (x k))} :=
  spec.holds_of_outer
    (Set.singleton_subset_iff.mpr (sys.output_outer out o R₀ traj k)) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
