module

public import CORALean.ContDynamics.LinearSys.Theorems.FlowIci

@[expose] public section

/-!
# The flow as a right derivative, the point itself dropped

`flow_Ici` minus its endpoint, which is the form
`integral_eq_sub_of_hasDeriv_right` asks for: `Ioi t` rather than `Ici t`
matters only there, since `HasDerivWithinAt.mono` gets from one to the other
for free.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same one-sided derivative with the point itself dropped, which is the
form `integral_eq_sub_of_hasDeriv_right` asks for. -/
theorem LinearSys.CanonicalClassicalTrajectory.flow_Ioi
    (traj : sys.CanonicalClassicalTrajectory T R₀ U x u)
    {a b t : ℝ} (hT : Set.Icc a b ⊆ T) (ht : t ∈ Set.Ico a b) :
    HasDerivWithinAt x (toRealMat sys.A *ᵥ x t + u t) (Set.Ioi t) t :=
  (traj.flow_Ici hT ht).mono Set.Ioi_subset_Ici_self

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
