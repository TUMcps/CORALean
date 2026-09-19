import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# Two-input runs of the integral equation

`PerturbedTrajectory` asks for a derivative at every point of `T`, which is
what `IntegralTrajectory` weakens for one signal and this weakens for two:
`x t = x 0 + ∫₀ᵗ (A x + u + w)`, so a run whose input or disturbance jumps still
counts. That matters for [1, Prop. 3] and [1, Prop. 5], whose right-hand sides
range over *every* point the particular solutions `Z_U(t)`, `Z_W(t)` contain,
and those are integrals of merely measurable signals: no derivative-everywhere
run realizes one, so the derivative reading turns the paper's `=` into `⊆`.

`measInput`/`measDisturbance` are each signal's own regularity, matching
`inputReach`'s "measurable enough to integrate, no more", and `cont` is
Carathéodory's local absolute continuity, without which `intervalIntegral`'s
junk value off integrability would admit an `x` that is no run at all.

No `init`/`R₀`, as in `PerturbedTrajectory`: Def. 6 and Def. 7 test one
starting point, which their own definitions pin.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory intervalIntegral

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A run under an input `u` and a disturbance `w`, each admissible and
measurable on `T`, with the flow stated as an integral equation. -/
structure LinearSys.PerturbedIntegralTrajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (U W : S n)
    (x u w : ℝ → Vec ℝ n) : Prop where
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  disturbance (t : ℝ) (ht : t ∈ T) : w t ∈ construct W
  measInput : AEStronglyMeasurable u (volume.restrict T)
  measDisturbance : AEStronglyMeasurable w (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) :
    x t = x 0 + ∫ s in (0:ℝ)..t, (toRealMat sys.A *ᵥ x s + u s + w s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
