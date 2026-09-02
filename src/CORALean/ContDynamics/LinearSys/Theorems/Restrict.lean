import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# A trajectory restricts to any smaller time domain

`HasDerivWithinAt.mono` is the whole content: a derivative within `T` is one
within every `T' ⊆ T`. This is what makes the domain a parameter worth having —
a run over all forward time is a run over `[0, τ]`, so a one-step guarantee
applies to it without restating the hypotheses.

`flow_Ici` and `flow_Ioi` go the other way, to a set `T` does *not* contain: the
measurability and fundamental-theorem lemmas ask for a one-sided derivative at
`t`, and `HasDerivWithinAt` only needs `T` to be a neighbourhood of `t` within
that side. `t ∈ Ico a b` with `Icc a b ⊆ T` gives it; the right endpoint is
excluded because there `T` runs out.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {sys : LinearSys 𝕋 n} {T T' : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n}

/-- Every run on `T` is a run on any smaller domain. -/
theorem LinearSys.Trajectory.restrict (traj : sys.Trajectory T R₀ U x u) (hT : T' ⊆ T) :
    sys.Trajectory T' R₀ U x u where
  init := traj.init
  input t ht := traj.input t (hT ht)
  flow t ht := (traj.flow t (hT ht)).mono hT

/-- The flow as a right derivative, wherever the domain still extends to the
right of `t`. -/
theorem LinearSys.Trajectory.flow_Ici (traj : sys.Trajectory T R₀ U x u) {a b t : ℝ}
    (hT : Set.Icc a b ⊆ T) (ht : t ∈ Set.Ico a b) :
    HasDerivWithinAt x (toRealMat sys.A *ᵥ x t + u t) (Set.Ici t) t :=
  (traj.flow t (hT ⟨ht.1, ht.2.le⟩)).mono_of_mem_nhdsWithin
    (mem_nhdsGE_iff_exists_Ico_subset.mpr
      ⟨b, ht.2, fun _ hs => hT ⟨le_trans ht.1 hs.1, hs.2.le⟩⟩)

/-- The same one-sided derivative with the point itself dropped, which is the
form `integral_eq_sub_of_hasDeriv_right` asks for. -/
theorem LinearSys.Trajectory.flow_Ioi (traj : sys.Trajectory T R₀ U x u) {a b t : ℝ}
    (hT : Set.Icc a b ⊆ T) (ht : t ∈ Set.Ico a b) :
    HasDerivWithinAt x (toRealMat sys.A *ᵥ x t + u t) (Set.Ioi t) t :=
  (traj.flow_Ici hT ht).mono Set.Ioi_subset_Ici_self

end CORALean.Real
