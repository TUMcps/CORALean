module

public import CORALean.ContDynamics.LinearSys.Operations.AutoReachFloat
public import CORALean.ContDynamics.LinearSys.Theorems.AutoStepFloatOuter
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `autoReachFloat` holds every run over `[0, t_end]`

[1, Alg. 2] in floats from `autoInitFloat`, which holds the invariant at `t₀ = 0`: `H(0)` is `X₀`
itself, and the constant and the `Ũ`-input have contributed `0`, which `{0}` holds. Then
`aux_autoRunFloat_outer` does the rest: the loop reached `t_end` or `autoReachFloat` is `none`, so
every time in `[0, t_end]` is in one of the windows.

## Inputs
* `sys` – linear system
* `X₀` – initial float zonotope
* `V` – input float zonotope
* `tend` – final float time
* `εmax` – admissible error
* `ζ` – error budget share
* `ηmax` – maximal Taylor order
* `fuel` – number of shrinkings
* `K` – number of steps

## Hypotheses
* none

## Conclusion
* every run is in the window covering its time

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Up to `K` iterations from a state holding the invariant reach one holding it, no earlier,
and if time advanced, every run over any time it covers is in one of the returned windows. -/
theorem LinearSys.aux_autoRunFloat_outer (sys : LinearSys 𝕋 n) {X₀ V : Zonotope (Vec 𝕋 n)}
    {tend : 𝕋}
    {εmax ζ : ℚ} {ηmax fuel : ℕ} : -- --- CONCL ---
    ∀ {K : ℕ} {s s' : LinearSys.AutoStateFloat 𝕋 n} {Ws : List (ℚ × ℚ × Zonotope (Vec 𝕋 n))},
      sys.autoRunFloat X₀ V tend εmax ζ ηmax fuel K s = some (s', Ws) →
      sys.IsAutoInvariantFloat X₀ V s →
      sys.IsAutoInvariantFloat X₀ V s' ∧ s.t ≤ s'.t ∧
        ∀ {T : ℝ} {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
          sys.IsCanonicalTrajectory (S := 𝒮) (Set.Icc 0 T) X₀.construct U x u →
          U ⊆ V.construct → s.t < s'.t → ∀ t ∈ Set.Icc (s.t : ℝ) s'.t, t ≤ T →
            ∃ w ∈ Ws, t ∈ Set.Icc (w.1 : ℝ) w.2.1 ∧ x t ∈ w.2.2.construct := by -- --- PROOF ---
  intro K
  induction K with
  | zero =>
    intro s s' Ws h hinv
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
    exact ⟨hinv, le_rfl, fun _ _ hlt => absurd hlt (lt_irrefl _)⟩
  | succ K ih =>
    intro s s' Ws h hinv
    simp only [LinearSys.autoRunFloat] at h
    split_ifs at h with hend
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
      exact ⟨hinv, le_rfl, fun _ _ hlt => absurd hlt (lt_irrefl _)⟩
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s1, R⟩, hstep, ⟨s2, Rs⟩, hrest, h⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (by simpa using h)).symm
      -- one iteration, then the rest of the run from the state it reached
      obtain ⟨hinv1, hlt1, hwin⟩ := sys.autoStepFloat_outer hinv _ _ hstep
      obtain ⟨hinv2, hle2, hrun⟩ := ih hrest hinv1
      refine ⟨hinv2, hlt1.le.trans hle2, fun {T U x u} traj hUV _ t ht htT => ?_⟩
      by_cases hts : t ≤ s1.t
      · exact ⟨_, List.mem_cons_self .., ⟨ht.1, hts⟩, hwin traj hUV t ⟨ht.1, hts⟩ htT⟩
      · rw [not_le] at hts
        have hlt2 : s1.t < s'.t := by
          have : (s1.t : ℝ) < s'.t := lt_of_lt_of_le hts ht.2
          exact_mod_cast this
        obtain ⟨w, hw, hwt, hxw⟩ := hrun traj hUV hlt2 t ⟨hts.le, ht.2⟩ htT
        exact ⟨w, List.mem_cons_of_mem _ hw, hwt, hxw⟩


omit [ToRat 𝕋] in
/-- `autoInitFloat` holds what a state owes at `t₀ = 0`. -/
theorem LinearSys.aux_autoInvariantFloat_init (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n))
    (tend : 𝕋) : -- --- CONCL ---
    sys.IsAutoInvariantFloat X₀ V (LinearSys.autoInitFloat X₀ tend) := by -- --- PROOF ---
  have hzero : (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope.construct := by
    have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (zero : 𝕋))
    rwa [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
  have hΓ0 : Real.MatExp.expIntegral (Scalar.toRealMat sys.A) 0 = 0 := by
    simp [Real.MatExp.expIntegral]
  refine ⟨le_rfl, by simp [LinearSys.autoInitFloat, toReal_zero],
    by simp [LinearSys.autoInitFloat, toReal_zero], fun x hx => ?_, ?_, fun y hy => ?_⟩
  · simpa [LinearSys.autoInitFloat, hΓ0] using hx
  · have h0 := Interval.mem_point (fun _ : Fin n => (zero : 𝕋))
    rw [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
    simpa [LinearSys.autoInitFloat, hΓ0] using h0
  · obtain ⟨u, -, -, rfl⟩ := hy
    refine ⟨0, hzero, 0, hzero, ?_⟩
    simp [LinearSys.autoInitFloat]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `[0, t_end]` from `X₀` under inputs in `V` is, at every time, in one of the
windows, the one covering that time. -/
theorem LinearSys.autoReachFloat_outer (sys : LinearSys 𝕋 n) {X₀ V : Zonotope (Vec 𝕋 n)} {tend : 𝕋}
    {εmax ζ : ℚ} {ηmax fuel K : ℕ} : -- --- CONCL ---
    ∀ Rs ∈ sys.autoReachFloat X₀ V tend εmax ζ ηmax fuel K,
      ∀ {T : ℝ} {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
        sys.IsCanonicalTrajectory (S := 𝒮) (Set.Icc 0 T) X₀.construct U x u →
        U ⊆ V.construct → ∀ t ∈ Set.Icc (0 : ℝ) (ToRat.toRat tend), t ≤ T →
          ∃ w ∈ Rs, t ∈ Set.Icc (w.1 : ℝ) w.2.1 ∧ x t ∈ w.2.2.construct := by -- --- PROOF ---
  intro Rs (h : sys.autoReachFloat X₀ V tend εmax ζ ηmax fuel K = some Rs)
  unfold LinearSys.autoReachFloat at h
  split_ifs at h with hpos
  split at h
  · exact absurd h (by simp)
  · rename_i s Ws hrun
    split_ifs at h with hend
    obtain rfl := Option.some.inj h
    obtain ⟨-, -, hcov⟩ := sys.aux_autoRunFloat_outer hrun
      (sys.aux_autoInvariantFloat_init X₀ V tend)
    intro traj hUV t ht htT
    have hlt : (LinearSys.autoInitFloat X₀ tend).t < s.t := lt_of_lt_of_le hpos.1 hend
    refine hcov traj hUV hlt t ⟨by simpa [LinearSys.autoInitFloat] using ht.1,
      ht.2.trans (by exact_mod_cast hend)⟩ htT

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
