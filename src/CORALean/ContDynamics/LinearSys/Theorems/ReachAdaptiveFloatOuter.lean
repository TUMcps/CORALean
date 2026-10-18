module

public import CORALean.ContDynamics.LinearSys.Theorems.InputSetFloatOuter
public import CORALean.ContDynamics.LinearSys.Operations.ReachAdaptiveFloat
public import CORALean.ContDynamics.LinearSys.Theorems.AdaptiveRunFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `reachAdaptiveFloat` holds every run, over windows covering the horizon

The windows of a successful run cover `[tStart, tFinal]` without a gap, and
every run of `ẋ = Ax + u` with `u(t) ∈ B U + c` from `X₀` is, at every time of a
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
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every time of `[tStart, tFinal]` lies in some step's window, and every run on
the horizon from `X₀` under inputs `u(t) ∈ B U + c` lies, at every time of a
window, in that window's set. -/
theorem LinearSys.reachAdaptiveFloat_outer (sys : LinearSys 𝕋 n)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ}
    {options : LinearSys.AdaptiveOptions 𝕋} {steps : List (LinearSys.AdaptiveStepInfo 𝕋 n)}
    (h : sys.reachAdaptiveFloat params options = some steps) : -- --- STMT ---
    (∀ t ∈ Set.Icc (params.tStart : ℝ) params.tFinal, ∃ (k : ℕ) (hk : k < steps.length),
        t ∈ Set.Icc (steps[k].tStart : ℝ) steps[k].tEnd) ∧
      ∀ {x u : ℝ → Vec ℝ n},
        sys.IsCanonicalTrajectory (S := 𝒮)
          (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
          ((fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) ''
            params.U.construct) x u →
        ∀ (k : ℕ) (hk : k < steps.length), ∀ t ∈ Set.Icc (steps[k].tStart : ℝ) steps[k].tEnd,
          x (t - params.tStart) ∈ steps[k].R.construct := by -- --- PROOF ---
  unfold LinearSys.reachAdaptiveFloat at h
  dsimp only at h
  split_ifs at h with htf
  set V := sys.inputSetFloat params.U with hV
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
  · -- the run's inputs `B u + c` are in `B U ⊕ c`'s float enclosure
    have hUV : (fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) ''
        params.U.construct ⊆ ContSet.construct V :=
      sys.inputSetFloat_outer params.U
    rw [← htf'] at traj
    exact hsnd _ (List.getElem_mem hk) traj hUV t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
