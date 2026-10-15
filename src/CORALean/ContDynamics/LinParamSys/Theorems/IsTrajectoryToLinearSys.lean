module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# A time-varying run is a run at any frozen matrix, with the drift as input

`IsConstTrajectory.toLinearSys` has no free counterpart at `'varParam'`: a run
drawing a fresh `A t` at every instant is a `LinearSys.IsCanonicalTrajectory` for no matrix
at all, which is why the closed form never applied there. It is one at *every*
matrix `Â` once the mismatch is paid into the input —
`A t x + u = Â x + ((A t - Â) x + u)` — and that is what this states.

The price is `hV`: the input set has to hold the drift `(A t - Â) x t` as well
as `u t`, so it is a set the caller supplies and not `U`. That makes the
statement a conservative linearization in the parameter rather than an identity,
and the drift is bounded by `‖A t - Â‖ ‖x t‖`, which `IsTrajectory.norm_le`
bounds a priori.

`Â` need not lie in `construct sys.A`; the theorems that use this ask it
separately, being about the matrix set's own enclosures. The linear run lives on a
measurable `T' ⊆ T`, where `x`'s continuity makes the drift measurable.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The time-varying reading at a frozen matrix: the parameter mismatch becomes
part of the input, and everything `LinearSys` proves applies again. -/
theorem LinParamSys.IsCanonicalTrajectory.toLinearSys {sys : LinParamSys 𝕄 n} {T : Set ℝ}
    {R₀ U V : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u A) (Â : Mat ℝ n n) {T' : Set ℝ} (hT' : T' ⊆ T)
    (hT'm : MeasurableSet T') (hV : ∀ t ∈ T', (A t - Â) *ᵥ x t + u t ∈ construct V) :
    (LinearSys.canonical Â : LinearSys ℝ n).IsCanonicalTrajectory T' R₀ V x
      (fun t => (A t - Â) *ᵥ x t + u t) where
  init := traj.init
  input := hV
  -- the drift: a measurable matrix times the state, continuous on the measurable `T'`
  meas := by
    have hx : AEStronglyMeasurable x (volume.restrict T') :=
      (traj.cont.mono hT').aestronglyMeasurable hT'm
    have hA := traj.measParam.mono_measure (Measure.restrict_mono hT' le_rfl)
    exact ((continuous_fst.matrix_mulVec continuous_snd).comp_aestronglyMeasurable
      ((hA.sub aestronglyMeasurable_const).prodMk hx)).add
      (traj.meas.mono_measure (Measure.restrict_mono hT' le_rfl))
  cont := traj.cont.mono hT'
  flow := fun t ht => by
    -- the same vector field, split at `Â` rather than at `A t`
    have hsplit : ∀ s, Â *ᵥ x s + ((A s - Â) *ᵥ x s + u s) = A s *ᵥ x s + u s := fun s => by
      rw [Matrix.sub_mulVec]
      abel
    simpa only [Scalar.toRealMat_real, hsplit] using traj.flow t (hT' ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
