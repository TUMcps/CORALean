import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal
import CORALean.ContDynamics.LinearSys.Operations.ManualReachFloat
import CORALean.ContDynamics.LinearSys.Theorems.ManualRunFloatOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec

/-!
# `manualReachFloat` holds every run over every window

[1, Alg. 1] in floats from `manualInitFloat`, which holds the invariant at `t₀ = 0`: `H(0)`
is `X₀` itself, and the constant and the `Ũ`-input have contributed `0`, which `{0}` holds.
`manualRunFloat_outer` does the rest, at the order `reachOrderFloat` admitted. Every input
`u(t) ∈ B U` is in `V = B U`'s float enclosure.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ToRat 𝕋] in
/-- `manualInitFloat` holds what a state owes at `t₀ = 0`. -/
theorem LinearSys.aux_manualInvariantFloat_init (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n)) :
    sys.ManualInvariantFloat X₀ V (LinearSys.manualInitFloat X₀) := by -- --- PROOF ---
  have hzero : (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope.construct := by
    have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (zero : 𝕋))
    rwa [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
  have hΓ0 : Real.MatExp.expIntegral (Scalar.toRealMat sys.A) 0 = 0 := by
    simp [Real.MatExp.expIntegral]
  refine ⟨le_rfl, by simp [LinearSys.manualInitFloat, toReal_zero],
    by simp [LinearSys.manualInitFloat, toReal_zero], fun x hx => ?_, ?_, fun y hy => ?_⟩
  · simpa [LinearSys.manualInitFloat, hΓ0] using hx
  · have h0 := Interval.mem_point (fun _ : Fin n => (zero : 𝕋))
    rw [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
    simpa [LinearSys.manualInitFloat, hΓ0] using h0
  · obtain ⟨u, -, -, rfl⟩ := hy
    simpa [LinearSys.manualInitFloat] using hzero


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `[0, tFinal - tStart]` from `X₀` under inputs `u(t) ∈ B U` is, at every
time of window `k`, in the `k`-th set. -/
theorem LinearSys.manualReachFloat_outer (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} {Rs : List (Zonotope (Vec 𝕋 n))}
    (h : sys.manualReachFloat B params options = some Rs) :
    ∃ N : ℕ, (N : ℝ) * toReal options.timeStep = (params.tFinal : ℝ) - params.tStart ∧
      Rs.length = N ∧ ∀ {x u : ℝ → Vec ℝ n},
        sys.Trajectory (S := fun k => Set (Vec ℝ k))
          (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.R0.construct
          ((Scalar.toRealMat B *ᵥ ·) '' params.U.construct) x u →
        ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.timeStep)
          (((k : ℝ) + 1) * toReal options.timeStep), x t ∈ Rs[k].construct := by -- --- PROOF ---
  obtain ⟨X₀, U, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinearSys.manualReachFloat, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨N, hN, η', hη', h⟩ := h
  obtain ⟨hΔt, hNΔt⟩ := Reach.steps_spec_toReal hN
  have hadm := (LinearSys.reachOrderFloat_spec hη').1
  set V := Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) B U with hV
  obtain ⟨hlen, hsnd⟩ := sys.manualRunFloat_outer hΔt hadm h
    (sys.aux_manualInvariantFloat_init X₀ V)
  refine ⟨N, hNΔt, hlen, fun {x u} traj k hk t ht => ?_⟩
  -- the run's inputs are in `B U`'s float enclosure
  have hUV : (Scalar.toRealMat B *ᵥ ·) '' U.construct ⊆ V.construct := by
    rintro _ ⟨w, hw, rfl⟩
    exact Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) B U
      (Set.mem_biUnion (Set.mem_singleton _) (Set.mem_image_of_mem _ hw))
  have hkN : (k : ℝ) + 1 ≤ N := by rw [hlen] at hk; exact_mod_cast hk
  refine hsnd traj hUV k hk t ⟨by simpa [LinearSys.manualInitFloat] using ht.1,
    by simpa [LinearSys.manualInitFloat] using ht.2⟩ ?_
  rw [← hNΔt]
  exact ht.2.trans (mul_le_mul_of_nonneg_right hkN hΔt.le)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
