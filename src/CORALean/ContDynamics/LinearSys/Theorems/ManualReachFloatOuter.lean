module

public import CORALean.ContDynamics.LinearSys.Theorems.InputSetFloatOuter
public import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal
public import CORALean.ContDynamics.LinearSys.Operations.ManualReachFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ManualRunFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `manualReachFloat` holds every run over every window

[1, Alg. 1] in floats from `aux_manualInitFloat`, which holds the invariant at `t₀ = 0`: `H(0)`
is `X₀` itself, and the constant and the `Ũ`-input have contributed `0`, which `{0}` holds.
`manualRunFloat_outer` does the rest, at the order `reachOrderFloat` admitted. Every input
`u(t) ∈ B U + c` is in `V = B U ⊕ c`'s float enclosure.

## Inputs
* `sys` – linear system
* `params` – reach parameters with initial and input sets
* `options` – reach options

## Hypotheses
* none

## Conclusion
* every run is in the window of its time

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ToRat 𝕋] in
/-- `aux_manualInitFloat` holds what a state owes at `t₀ = 0`. -/
theorem LinearSys.aux_manualInvariantFloat_init (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n)) :
    sys.ManualInvariantFloat X₀ V (LinearSys.aux_manualInitFloat X₀) := by -- --- PROOF ---
  have hzero : (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope.construct := by
    have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (zero : 𝕋))
    rwa [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
  have hΓ0 : Real.MatExp.expIntegral (Scalar.toRealMat sys.A) 0 = 0 := by
    simp [Real.MatExp.expIntegral]
  refine ⟨le_rfl, by simp [LinearSys.aux_manualInitFloat, toReal_zero],
    by simp [LinearSys.aux_manualInitFloat, toReal_zero], fun x hx => ?_, ?_, fun y hy => ?_⟩
  · simpa [LinearSys.aux_manualInitFloat, hΓ0] using hx
  · have h0 := Interval.mem_point (fun _ : Fin n => (zero : 𝕋))
    rw [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
    simpa [LinearSys.aux_manualInitFloat, hΓ0] using h0
  · obtain ⟨u, -, -, rfl⟩ := hy
    simpa [LinearSys.aux_manualInitFloat] using hzero


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `[0, tFinal - tStart]` from `X₀` under inputs `u(t) ∈ B U + c` is, at every
time of window `k`, in the `k`-th set. -/
theorem LinearSys.manualReachFloat_outer (sys : LinearSys 𝕋 n)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} : -- --- CONCL ---
    ∀ Rs ∈ sys.manualReachFloat params options,
      ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
        Rs.length = N ∧ ∀ {x u : ℝ → Vec ℝ n},
          sys.IsCanonicalTrajectory (S := 𝒮)
            (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
            ((fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) ''
              params.U.construct) x u →
          ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
            (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[k].construct := by -- --- PROOF ---
  intro Rs (h : sys.manualReachFloat params options = some Rs)
  obtain ⟨X₀, U, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinearSys.manualReachFloat, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨N, hN, η', hη', h⟩ := h
  obtain ⟨hΔt, hNΔt⟩ := Reach.steps_spec_toReal _ hN
  have hadm := (LinearSys.reachOrderFloat_spec _ hη').1
  set V := sys.inputSetFloat U with hV
  obtain ⟨hlen, hsnd⟩ := sys.manualRunFloat_outer hΔt hadm h
    (sys.aux_manualInvariantFloat_init X₀ V)
  refine ⟨N, hNΔt, hlen, fun {x u} traj k hk t ht => ?_⟩
  -- the run's inputs `B u + c` are in `B U ⊕ c`'s float enclosure
  have hUV : (fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) ''
      U.construct ⊆ ContSet.construct V :=
    sys.inputSetFloat_outer U
  have hkN : (k : ℝ) + 1 ≤ N := by rw [hlen] at hk; exact_mod_cast hk
  refine hsnd traj hUV k hk t ⟨by simpa [LinearSys.aux_manualInitFloat] using ht.1,
    by simpa [LinearSys.aux_manualInitFloat] using ht.2⟩ ?_
  rw [← hNΔt]
  exact ht.2.trans (mul_le_mul_of_nonneg_right hkN hΔt.le)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
