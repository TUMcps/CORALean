module

public import CORALean.ContDynamics.LinearSys.Operations.SupportLower
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetEq
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegralZero
public import CORALean.ContSet.ContSet.Theorems.IsGreatestImageConvexHull

@[expose] public section

/-!
# [1, Alg. 1 (upper bounds)]'s line 13 is no upper bound for a centre outside `U`

For `A = 0`, `X₀ = {0}`, the simplex `U = conv{c₀, c₀ + e₁, c₀ + e₂, c₀ + e₃}` with
`c₀ = (-3, -3, -3)`, `ℓ = (1, 1, 1)`, `Δt = 1` and `k = 1`, the centre of the enclosing box
`[-3, -2]³` is `ũ = (-5/2, -5/2, -5/2)`, which is outside `U`. Lines 8-11 of the upper bounds
are lines 8-10 and 14 of the lower bounds with the same `U₀ = U - ũ`, so the quantities line 13
reads, `ρ(H(t_k), ℓ)` and `ρ(P̂_U(t_{k+1}), ℓ)`, are those of `supportLower`; the curvature
enclosure `C = F X₀ ⊕ G ũ` of line 5 is `{0}` for `A = 0`, and so `ρ(C, d_1) = 0`. Line 13 reads
`max{-15/2, -15} + 0 + 2 · (-1/2) = -17/2`, while the exact reachable set at `t = 1 ∈ τ₁ = [1, 2]`
is `U` and holds the state `c₀ + e₁` with `ℓ = -8`: a "bound" below the support function.

The tree's `supportUpper` cannot express this: its `Recentre.recentre U` always holds the
origin, which is the repair, so it enlarges `U - ũ` and stays above the support function.

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
open Matrix ContSet Scalar NormedSpace


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.supportUpper_centre_counterexample :
    let sys : LinearSys ℝ 3 := ⟨0⟩
    let U : Set (Vec ℝ 3) := convexHull ℝ
      {![-3, -3, -3], ![-2, -3, -3], ![-3, -2, -3], ![-3, -3, -2]}
    let ℓ : Vec ℝ 3 →ₗ[ℝ] ℝ :=
      (LinearMap.proj 0 : Vec ℝ 3 →ₗ[ℝ] ℝ) + (LinearMap.proj 1 : Vec ℝ 3 →ₗ[ℝ] ℝ) +
        (LinearMap.proj 2 : Vec ℝ 3 →ₗ[ℝ] ℝ)
    let ũ : Vec ℝ 3 := ![-5 / 2, -5 / 2, -5 / 2]
    let S := sys.supportLower 1 (fun _ => 0) (fun _ => ![-2, -3, -3]) ũ ℓ
    ũ ∉ U ∧
    (∀ i, IsLeast ((fun x : Vec ℝ 3 => x i) '' U) (-3) ∧
      IsGreatest ((fun x : Vec ℝ 3 => x i) '' U) (-2)) ∧
    IsGreatest (ℓ '' U) (ℓ ![-2, -3, -3]) ∧
    max (S 1).ρH (S 2).ρH + 0 + (S 2).ρP = -17 / 2 ∧
    ∃ t ∈ Set.Icc (1 : ℝ) 2, ∃ y ∈ sys.reachSet (S := 𝒮)
      (Set.Icc 0 t) ({0} : Set (Vec ℝ 3)) U t, -17 / 2 < ℓ y := by -- --- PROOF ---
  intro sys U ℓ ũ S
  have hS : ∀ s ∈ ({![-3, -3, -3], ![-2, -3, -3], ![-3, -2, -3], ![-3, -3, -2]} :
      Set (Vec ℝ 3)),
      s = ![-3, -3, -3] ∨ s = ![-2, -3, -3] ∨ s = ![-3, -2, -3] ∨ s = ![-3, -3, -2] := by
    intro s hs
    simpa using hs
  have hmax : IsGreatest (ℓ '' U) (ℓ ![-2, -3, -3]) :=
    isGreatest_image_convexHull ℓ ⟨![-2, -3, -3], by simp, rfl⟩ fun s hs => by
      rcases hS s hs with rfl | rfl | rfl | rfl <;> simp [ℓ] <;> norm_num
  -- next step of the computation
  have hℓũ : ℓ ũ = -15 / 2 := by simp [ℓ, ũ]; norm_num
  have hℓe : ℓ ![-2, -3, -3] = -8 := by simp [ℓ]; norm_num
  have hA : sys.A = 0 := rfl
  have h0 : toRealMat sys.A = 0 := by simp [hA]
  have hbox : ∀ i : Fin 3, IsLeast ((fun x : Vec ℝ 3 => x i) '' U) (-3) ∧
      IsGreatest ((fun x : Vec ℝ 3 => x i) '' U) (-2) := by
    intro i
    refine ⟨⟨⟨![-3, -3, -3], subset_convexHull ℝ _ (by simp), by fin_cases i <;> simp⟩, ?_⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact convexHull_min (fun s hs => by
        rcases hS s hs with rfl | rfl | rfl | rfl <;> fin_cases i <;> simp <;> norm_num)
        (convex_halfSpace_ge (LinearMap.proj i : Vec ℝ 3 →ₗ[ℝ] ℝ).isLinear (-3)) hx
    -- next step of the computation
    · fin_cases i
      · exact isGreatest_image_convexHull (LinearMap.proj 0 : Vec ℝ 3 →ₗ[ℝ] ℝ)
          ⟨![-2, -3, -3], by simp, by simp⟩ fun s hs => by
            rcases hS s hs with rfl | rfl | rfl | rfl <;> simp <;> norm_num
      · exact isGreatest_image_convexHull (LinearMap.proj 1 : Vec ℝ 3 →ₗ[ℝ] ℝ)
          ⟨![-3, -2, -3], by simp, by simp⟩ fun s hs => by
            rcases hS s hs with rfl | rfl | rfl | rfl <;> simp <;> norm_num
      · exact isGreatest_image_convexHull (LinearMap.proj 2 : Vec ℝ 3 →ₗ[ℝ] ℝ)
          ⟨![-3, -3, -2], by simp, by simp⟩ fun s hs => by
            rcases hS s hs with rfl | rfl | rfl | rfl <;> simp <;> norm_num
  -- next step of the computation
  refine ⟨?_, hbox, hmax, ?_, ?_⟩
  · intro h
    have := hmax.2 ⟨ũ, h, rfl⟩
    rw [hℓũ, hℓe] at this
    norm_num at this
  · simp only [S, LinearSys.supportLower]
    simp [h0, MatExp.expIntegral_zero, hℓũ]
    rw [hℓe]
    norm_num
  · have hfin : ({![-3, -3, -3], ![-2, -3, -3], ![-3, -2, -3], ![-3, -3, -2]} :
        Set (Vec ℝ 3)).Finite := Set.toFinite _
    -- next step of the computation
    have hbdd : Bornology.IsBounded U := (hfin.isCompact_convexHull ℝ).isBounded
    refine ⟨1, ⟨le_rfl, one_le_two⟩, ![-2, -3, -3], ?_, by rw [hℓe]; norm_num⟩
    rw [LinearSys.reachSet_eq (S := 𝒮) sys ({0} : Set (Vec ℝ 3)) U
      zero_le_one hbdd]
    have hmem := sys.expIntegral_mem_inputReach (S := 𝒮) zero_le_one
      (U := U) (v := ![-2, -3, -3]) (subset_convexHull ℝ _ (by simp))
    simp only [h0, MatExp.expIntegral_zero, Matrix.one_mulVec, one_smul] at hmem
    have := Set.add_mem_add (s := (exp ((1 : ℝ) • toRealMat sys.A)).mulVecLin ''
      construct ({0} : Set (Vec ℝ 3))) (a := 0) ⟨0, rfl, by simp⟩ hmem
    simpa using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
