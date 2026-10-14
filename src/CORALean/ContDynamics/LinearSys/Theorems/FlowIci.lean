module

public import CORALean.ContDynamics.LinearSys.Definitions.CanonicalClassicalTrajectory

@[expose] public section

/-!
# The flow as a right derivative

`CanonicalClassicalTrajectory.flow` states the derivative within `T`, which is too weak
for the one-sided fundamental theorem of calculus `CanonicalClassicalTrajectory.trajectory`
builds on: it asks for a derivative within `Ici t`, and `T` need not contain a
neighbourhood of `t` on the left. `Set.Icc a b ⊆ T` with `t ∈ Ico a b` is what buys it —
`T` still extends right of `t`, whatever it does on the left.
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

/-- The flow as a right derivative, wherever the domain still extends to the
right of `t`. -/
theorem LinearSys.CanonicalClassicalTrajectory.flow_Ici
    (traj : sys.CanonicalClassicalTrajectory T R₀ U x u)
    {a b t : ℝ} (hT : Set.Icc a b ⊆ T) (ht : t ∈ Set.Ico a b) :
    HasDerivWithinAt x (toRealMat sys.A *ᵥ x t + u t) (Set.Ici t) t :=
  (traj.flow t (hT ⟨ht.1, ht.2.le⟩)).mono_of_mem_nhdsWithin
    (mem_nhdsGE_iff_exists_Ico_subset.mpr
      ⟨b, ht.2, fun _ hs => hT ⟨le_trans ht.1 hs.1, hs.2.le⟩⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
