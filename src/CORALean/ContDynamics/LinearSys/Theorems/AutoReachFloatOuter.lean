module

public import CORALean.ContDynamics.LinearSys.Operations.AutoReachFloat
public import CORALean.ContDynamics.LinearSys.Theorems.AutoRunFloatOuter
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `autoReachFloat` holds every run over `[0, t_end]`

[1, Alg. 2] in floats from `autoInitFloat`, which holds the invariant at `t₀ = 0`: `H(0)` is `X₀`
itself, and the constant and the `Ũ`-input have contributed `0`, which `{0}` holds. Then
`autoRunFloat_outer` does the rest: the loop reached `t_end` or `autoReachFloat` is `none`, so
every time in `[0, t_end]` is in one of the windows.

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

omit [ToRat 𝕋] in
/-- `autoInitFloat` holds what a state owes at `t₀ = 0`. -/
theorem LinearSys.aux_autoInvariantFloat_init (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n))
    (tend : 𝕋) :
    sys.AutoInvariantFloat X₀ V (LinearSys.autoInitFloat X₀ tend) := by -- --- PROOF ---
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
    {εmax ζ : ℚ} {ηmax fuel K : ℕ} {Rs : List (ℚ × ℚ × Zonotope (Vec 𝕋 n))}
    (h : sys.autoReachFloat X₀ V tend εmax ζ ηmax fuel K = some Rs) : -- --- STMT ---
    ∀ {T : ℝ} {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
      sys.IsCanonicalTrajectory (S := 𝒮) (Set.Icc 0 T) X₀.construct U x u →
      U ⊆ V.construct → ∀ t ∈ Set.Icc (0 : ℝ) (ToRat.toRat tend), t ≤ T →
        ∃ w ∈ Rs, t ∈ Set.Icc (w.1 : ℝ) w.2.1 ∧ x t ∈ w.2.2.construct := by -- --- PROOF ---
  unfold LinearSys.autoReachFloat at h
  split_ifs at h with hpos
  split at h
  · exact absurd h (by simp)
  · rename_i s Ws hrun
    split_ifs at h with hend
    obtain rfl := Option.some.inj h
    obtain ⟨-, -, hcov⟩ := sys.autoRunFloat_outer hrun
      (sys.aux_autoInvariantFloat_init X₀ V tend)
    intro traj hUV t ht htT
    have hlt : (LinearSys.autoInitFloat X₀ tend).t < s.t := lt_of_lt_of_le hpos.1 hend
    refine hcov traj hUV hlt t ⟨by simpa [LinearSys.autoInitFloat] using ht.1,
      ht.2.trans (by exact_mod_cast hend)⟩ htT

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
