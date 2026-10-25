module

public import CORALean.ContDynamics.LinearSys.Theorems.InputSetFloatOuter
public import CORALean.ContDynamics.LinearSys.Operations.ReachAdaptiveFloat
public import CORALean.ContDynamics.LinearSys.Theorems.AdaptiveStepFloatOuter
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

## Inputs
* `sys` – linear system
* `params` – reach parameters with initial and input sets
* `options` – adaptive options

## Hypotheses
* none

## Conclusion
* the steps' windows cover the horizon and hold every run

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}

/-- A successful run from a state holding the invariant has either already
reached `t_f`, or its windows cover `[t₀ + t_i, t₀ + t_f]`; and each window
holds every run at every time of it. -/
theorem LinearSys.aux_adaptiveRunFloat_outer (sys : LinearSys 𝕋 n) {X₀ V : Zonotope (Vec 𝕋 n)}
    {t₀ tf : ℚ} {options : LinearSys.AdaptiveOptions 𝕋} : -- --- CONCL ---
    ∀ {k : ℕ} {s : LinearSys.AdaptiveState 𝕋 n} {steps : List (LinearSys.AdaptiveStepInfo 𝕋 n)},
      sys.adaptiveRunFloat X₀ V t₀ tf options k s = some steps → sys.IsAdaptiveInvariant V s →
      ((tf : ℝ) ≤ s.t ∨ ∀ t ∈ Set.Icc ((t₀ : ℝ) + s.t) ((t₀ : ℝ) + tf),
          ∃ r ∈ steps, t ∈ Set.Icc (r.tStart : ℝ) r.tEnd) ∧
        ∀ r ∈ steps, ∀ {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
          sys.IsCanonicalTrajectory (S := 𝒮) (Set.Icc 0 (tf : ℝ)) X₀.construct U x u →
          U ⊆ V.construct → ∀ t ∈ Set.Icc (r.tStart : ℝ) r.tEnd,
            x (t - t₀) ∈ r.R.construct := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro s steps h _
    simp only [LinearSys.adaptiveRunFloat] at h
    split_ifs at h with hle
    obtain rfl := (Option.some.inj h).symm
    exact ⟨Or.inl (by exact_mod_cast hle), by simp⟩
  | succ k ih =>
    intro s steps h hinv
    simp only [LinearSys.adaptiveRunFloat] at h
    split_ifs at h with hle
    · obtain rfl := (Option.some.inj h).symm
      exact ⟨Or.inl (by exact_mod_cast hle), by simp⟩
    -- one step, then the rest of the run from the state it reached
    cases hstep : sys.adaptiveStepFloat X₀ V t₀ tf options s with
    | none => simp [hstep] at h
    | some rs =>
      obtain ⟨r, s'⟩ := rs
      simp only [hstep, Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      obtain ⟨hinv', hlt, hrs, hre, hsound⟩ := sys.adaptiveStepFloat_outer hinv _ _ hstep
      obtain ⟨hcov, hsnd⟩ := ih hrest hinv'
      have hre' : (r.tEnd : ℝ) = t₀ + min (s'.t : ℝ) tf := by rw [hre]; push_cast; rfl
      have hrs' : (r.tStart : ℝ) = t₀ + s.t := by rw [hrs]; push_cast; rfl
      refine ⟨Or.inr fun t ht => ?_, fun r' hr' U x u traj hUV t ht => ?_⟩
      · -- inside this step's window, or past the next state's time
        by_cases htle : t ≤ t₀ + min (s'.t : ℝ) tf
        · exact ⟨r, List.mem_cons_self .., by rw [hrs', hre']; exact ⟨ht.1, htle⟩⟩
        · have hst : (s'.t : ℝ) < tf := by
            by_contra hc
            exact htle (by rw [min_eq_right (not_lt.mp hc)]; exact ht.2)
          rw [min_eq_left hst.le] at htle
          rcases hcov with hc | hc
          · exact absurd hc (not_le.mpr hst)
          · obtain ⟨r', hr', hmem⟩ := hc t ⟨(not_le.mp htle).le, ht.2⟩
            exact ⟨r', List.mem_cons_of_mem _ hr', hmem⟩
      · rcases List.mem_cons.mp hr' with rfl | hr'
        · rw [hrs', hre'] at ht
          exact hsound traj hUV (t - t₀) ⟨by linarith [ht.1],
            by linarith [ht.2, min_le_left (s'.t : ℝ) tf]⟩
            (by linarith [ht.2, min_le_right (s'.t : ℝ) tf])
        · exact hsnd r' hr' traj hUV t ht

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every time of `[tStart, tFinal]` lies in some step's window, and every run on
the horizon from `X₀` under inputs `u(t) ∈ B U + c` lies, at every time of a
window, in that window's set. -/
theorem LinearSys.reachAdaptiveFloat_outer (sys : LinearSys 𝕋 n)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ}
    {options : LinearSys.AdaptiveOptions 𝕋} : -- --- CONCL ---
    ∀ steps ∈ sys.reachAdaptiveFloat params options,
      (∀ t ∈ Set.Icc (params.tStart : ℝ) params.tFinal, ∃ (k : ℕ) (hk : k < steps.length),
          t ∈ Set.Icc (steps[k].tStart : ℝ) steps[k].tEnd) ∧
        ∀ {x u : ℝ → Vec ℝ n},
          sys.IsCanonicalTrajectory (S := 𝒮)
            (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
            ((fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) ''
              params.U.construct) x u →
          ∀ (k : ℕ) (hk : k < steps.length), ∀ t ∈ Set.Icc (steps[k].tStart : ℝ) steps[k].tEnd,
            x (t - params.tStart) ∈ steps[k].R.construct := by -- --- PROOF ---
  intro steps (h : sys.reachAdaptiveFloat params options = some steps)
  unfold LinearSys.reachAdaptiveFloat at h
  dsimp only at h
  split_ifs at h with htf
  set V := sys.inputSetFloat params.U with hV
  -- nothing is contributed by time `0`
  have hinv : sys.IsAdaptiveInvariant V (⟨0, ⟨zero, zero⟩,
      mulDown (ratUp (params.tFinal - params.tStart)) options.μ, 0, 0,
      (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope⟩ : LinearSys.AdaptiveState 𝕋 n) := by
    refine ⟨le_rfl, by simp [toReal_zero], by simp [toReal_zero], fun y hy => ?_⟩
    obtain ⟨u, -, -, rfl⟩ := hy
    have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (zero : 𝕋))
    rw [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
    simpa [Real.MatExp.expIntegral_mulVec _ _ (le_refl (0 : ℝ))] using h0
  obtain ⟨hcov, hsnd⟩ := sys.aux_adaptiveRunFloat_outer h hinv
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
