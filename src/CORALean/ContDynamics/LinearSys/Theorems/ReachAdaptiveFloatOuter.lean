module

public import CORALean.ContDynamics.LinearSys.Operations.ReachAdaptiveFloat
public import CORALean.ContDynamics.LinearSys.Theorems.AdaptiveRunFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec

@[expose] public section

/-!
# `reachAdaptiveFloat` holds every run, over windows covering the horizon

The windows of a successful run cover `[tStart, tFinal]` without a gap, and
every run of `ẋ = Ax + u` with `u(t) ∈ B U` from `X₀` is, at every time of a
window, in that window's set. [1, Alg. 1] in floats is sound whatever it tunes: whatever step,
truncation order and reduction order [1]'s `Alg. 2` and `Alg. 3` chose, the
initial state holds the invariant (nothing contributed by time `0`) and every
step keeps it (`adaptiveStepFloat_outer`).

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every time of `[tStart, tFinal]` lies in some step's window, and every run on
the horizon from `X₀` under inputs `u(t) ∈ B U` lies, at every time of a
window, in that window's set. -/
theorem LinearSys.reachAdaptiveFloat_outer (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ}
    {options : LinearSys.AdaptiveOptions 𝕋} {steps : List (LinearSys.AdaptiveStepInfo 𝕋 n)}
    (h : sys.reachAdaptiveFloat B params options = some steps) :
    (∀ t ∈ Set.Icc (params.tStart : ℝ) params.tFinal, ∃ (k : ℕ) (hk : k < steps.length),
        t ∈ Set.Icc (steps[k].tStart : ℝ) steps[k].tEnd) ∧
      ∀ {x u : ℝ → Vec ℝ n},
        sys.Trajectory (S := 𝒮)
          (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
          ((Scalar.toRealMat B *ᵥ ·) '' params.U.construct) x u →
        ∀ (k : ℕ) (hk : k < steps.length), ∀ t ∈ Set.Icc (steps[k].tStart : ℝ) steps[k].tEnd,
          x (t - params.tStart) ∈ steps[k].R.construct := by -- --- PROOF ---
  unfold LinearSys.reachAdaptiveFloat at h
  dsimp only at h
  split_ifs at h with htf
  set V := Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) B params.U with hV
  -- nothing is contributed by time `0`
  have hinv : sys.AdaptiveInvariant V (⟨0, zero, zero,
      mulDown (ratUp (params.tFinal - params.tStart)) options.μ, 0, 0,
      (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope⟩ : LinearSys.AdaptiveState 𝕋 n) := by
    refine ⟨le_rfl, by simp [toReal_zero], by simp [toReal_zero], fun y hy => ?_⟩
    obtain ⟨u, -, -, rfl⟩ := hy
    have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (zero : 𝕋))
    rw [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
    simpa [Real.MatExp.expIntegral_mulVec _ _ (le_refl (0 : ℝ))] using h0
  obtain ⟨hcov, hsnd⟩ := sys.adaptiveRunFloat_outer h hinv
  have htf' : (((params.tFinal - params.tStart : ℚ)) : ℝ) = params.tFinal - params.tStart := by
    push_cast; ring
  refine ⟨fun t ht => ?_, fun {x u} traj k hk t ht => ?_⟩
  · rcases hcov with hc | hc
    · exact absurd hc (by push_cast; exact_mod_cast not_le.mpr htf)
    · obtain ⟨r, hr, hmem⟩ := hc t ⟨by push_cast; linarith [ht.1], by
        rw [htf']; linarith [ht.2]⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
      exact ⟨k, hk, hmem⟩
  · -- the run's inputs are in `B U`'s float enclosure
    have hUV : (Scalar.toRealMat B *ᵥ ·) '' params.U.construct ⊆ V.construct := by
      rintro _ ⟨w, hw, rfl⟩
      exact Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) B params.U
        (Set.mem_biUnion (Set.mem_singleton _) (Set.mem_image_of_mem _ hw))
    rw [← htf'] at traj
    exact hsnd _ (List.getElem_mem hk) traj hUV t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
