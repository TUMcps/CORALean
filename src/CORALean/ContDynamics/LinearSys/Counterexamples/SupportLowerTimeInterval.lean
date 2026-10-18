module

public import CORALean.ContDynamics.LinearSys.Operations.SupportLower
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactEq
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegralZero
public import CORALean.ContSet.ContSet.Theorems.IsGreatestImageConvexHull
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# [1, Alg. 1 (lower bounds)]'s line 16 is no lower bound for a center outside `U`

For `A = 0`, `X₀ = {0}`, the simplex `U = conv{0, e₁, e₂, e₃} ⊂ ℝ³`, `ℓ = (1, 1, 1)` and `Δt = 1`
the center of the enclosing box `[0, 1]³` is `ũ = (1/2, 1/2, 1/2)`, which is outside `U`. Line 16
reads `ρ(Ř(τ₀), ℓ) = 3/2` there (`supportLower` at `k = 1`), while the exact reachable set at
`t ∈ [0, 1]` is `tU` (`reachSetExact_eq` with `e^{0} = I`), whose support function along `ℓ` over
`τ₀ = [0, 1]` is `1`: a "lower bound" above the support function.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.supportLower_timeInterval_counterexample : -- --- STMT ---
    let sys : LinearSys ℝ 3 := LinearSys.canonical 0
    let U : Set (Vec ℝ 3) := convexHull ℝ {![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1]}
    let ℓ : Vec ℝ 3 →ₗ[ℝ] ℝ :=
      (LinearMap.proj 0 : Vec ℝ 3 →ₗ[ℝ] ℝ) + (LinearMap.proj 1 : Vec ℝ 3 →ₗ[ℝ] ℝ) +
        (LinearMap.proj 2 : Vec ℝ 3 →ₗ[ℝ] ℝ)
    let ũ : Vec ℝ 3 := ![1 / 2, 1 / 2, 1 / 2]
    ũ ∉ U ∧
    (∀ i, IsLeast ((fun x : Vec ℝ 3 => x i) '' U) 0 ∧
      IsGreatest ((fun x : Vec ℝ 3 => x i) '' U) 1) ∧
    IsGreatest (ℓ '' U) (ℓ ![1, 0, 0]) ∧
    (sys.supportLower 1 (fun _ => 0) (fun _ => ![1, 0, 0]) ũ ℓ 1).ρRτ = 3 / 2 ∧
    IsGreatest {r | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ sys.reachSetExact (S := 𝒮)
      (Set.Icc 0 t) ({0} : Set (Vec ℝ 3)) U t, r = ℓ y} 1 := by -- --- PROOF ---
  intro sys U ℓ ũ
  have hS : ∀ s ∈ ({![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} : Set (Vec ℝ 3)),
      s = ![0, 0, 0] ∨ s = ![1, 0, 0] ∨ s = ![0, 1, 0] ∨ s = ![0, 0, 1] := by
    intro s hs
    simpa using hs
  have hmax : IsGreatest (ℓ '' U) (ℓ ![1, 0, 0]) :=
    isGreatest_image_convexHull ℓ ⟨![1, 0, 0], by simp, rfl⟩ fun s hs => by
      rcases hS s hs with rfl | rfl | rfl | rfl <;> simp [ℓ]
  -- next step of the computation
  have hℓũ : ℓ ũ = 3 / 2 := by simp [ℓ, ũ]; norm_num
  -- next step of the computation
  have hℓe : ℓ ![1, 0, 0] = 1 := by simp [ℓ]
  have hbox : ∀ i : Fin 3, IsLeast ((fun x : Vec ℝ 3 => x i) '' U) 0 ∧
      IsGreatest ((fun x : Vec ℝ 3 => x i) '' U) 1 := by
    intro i
    refine ⟨⟨⟨![0, 0, 0], subset_convexHull ℝ _ (by simp), by fin_cases i <;> simp⟩, ?_⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact convexHull_min (fun s hs => by
        rcases hS s hs with rfl | rfl | rfl | rfl <;> fin_cases i <;> simp)
        (convex_halfSpace_ge (LinearMap.proj i : Vec ℝ 3 →ₗ[ℝ] ℝ).isLinear 0) hx
    -- next step of the computation
    · fin_cases i
      · exact isGreatest_image_convexHull (LinearMap.proj 0 : Vec ℝ 3 →ₗ[ℝ] ℝ)
          ⟨![1, 0, 0], by simp, by simp⟩ fun s hs => by
            rcases hS s hs with rfl | rfl | rfl | rfl <;> simp
      · exact isGreatest_image_convexHull (LinearMap.proj 1 : Vec ℝ 3 →ₗ[ℝ] ℝ)
          ⟨![0, 1, 0], by simp, by simp⟩ fun s hs => by
            rcases hS s hs with rfl | rfl | rfl | rfl <;> simp
      · exact isGreatest_image_convexHull (LinearMap.proj 2 : Vec ℝ 3 →ₗ[ℝ] ℝ)
          ⟨![0, 0, 1], by simp, by simp⟩ fun s hs => by
            rcases hS s hs with rfl | rfl | rfl | rfl <;> simp
  -- next step of the computation
  refine ⟨?_, ?_, hmax, ?_, ?_⟩
  · intro h
    have := hmax.2 ⟨ũ, h, rfl⟩
    rw [hℓũ, hℓe] at this
    norm_num at this
  · exact hbox
  · simp only [LinearSys.supportLower]
    have hA : sys.A = 0 := rfl
    simp [hA, MatExp.expIntegral_zero, hℓũ]
    norm_num
  -- next step of the computation
  · have hA : sys.A = 0 := rfl
    have hfin : ({![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} : Set (Vec ℝ 3)).Finite :=
      Set.toFinite _
    have hbdd : Bornology.IsBounded U := (hfin.isCompact_convexHull ℝ).isBounded
    have hℓ1 : ∀ x ∈ U, ℓ x ≤ 1 := fun x hx => by simpa [hℓe] using hmax.2 ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ![1, 0, 0], ?_, by simp [hℓe]⟩
      rw [LinearSys.reachSetExact_eq (S := 𝒮) sys ({0} : Set (Vec ℝ 3)) U
        zero_le_one hbdd]
      -- next step of the computation
      have hmem := sys.expIntegral_mem_inputReach (S := 𝒮) zero_le_one
        (U := U) (v := ![1, 0, 0]) (subset_convexHull ℝ _ (by simp))
      have h0 : toRealMat sys.A = 0 := by simp [hA]
      simp only [h0, MatExp.expIntegral_zero, Matrix.one_mulVec, one_smul] at hmem
      have := Set.add_mem_add (s := (exp ((1 : ℝ) • toRealMat sys.A)).mulVecLin ''
        construct ({0} : Set (Vec ℝ 3))) (a := 0) ⟨0, rfl, by simp⟩ hmem
      simpa using this
    -- next step of the computation
    · rintro r ⟨t, ⟨ht0, ht1⟩, y, hy, rfl⟩
      rw [LinearSys.reachSetExact_eq (S := 𝒮) sys ({0} : Set (Vec ℝ 3)) U ht0
        hbdd] at hy
      obtain ⟨a, ⟨x, hx, rfl⟩, z, ⟨u, hu, hmeas, rfl⟩, rfl⟩ := hy
      have hx0 : x = 0 := hx
      have h0 : toRealMat sys.A = 0 := by simp [hA]
      have hbound : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖u s‖ ≤ 1 := by
        intro s hs
        refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
        -- next step of the computation
        rw [Real.norm_eq_abs, abs_le]
        have hi := (hbox i).1.2 ⟨u s, hu s hs, rfl⟩
        have hg := (hbox i).2.2 ⟨u s, hu s hs, rfl⟩
        constructor <;> linarith
      have hint : IntervalIntegrable u volume 0 t :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le ht0).mpr
          (Integrable.of_bound hmeas 1
            ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hbound)))
      have hz : (∫ s in (0 : ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
          = ∫ s in (0 : ℝ)..t, u s := by
        -- next step of the computation
        simp [h0]
      have hxz : (exp (t • toRealMat sys.A)).mulVecLin x = 0 := by
        simp [hx0]
      show ℓ ((exp (t • toRealMat sys.A)).mulVecLin x + _) ≤ 1
      rw [hxz, hz, zero_add]
      let L : Vec ℝ 3 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ℓ
      have hcomm : ℓ (∫ s in (0 : ℝ)..t, u s) = ∫ s in (0 : ℝ)..t, ℓ (u s) :=
        (L.intervalIntegral_comp_comm hint).symm
      rw [hcomm]
      -- next step of the computation
      calc ∫ s in (0 : ℝ)..t, ℓ (u s) ≤ ∫ _ in (0 : ℝ)..t, (1 : ℝ) :=
            intervalIntegral.integral_mono_on ht0
              ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht0).mpr
                (L.integrable_comp ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht0).mp hint)))
              (by simp)
              fun s hs => hℓ1 _ (hu s hs)
        _ = t := by simp
        _ ≤ 1 := ht1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
