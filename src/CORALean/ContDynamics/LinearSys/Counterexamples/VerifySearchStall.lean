module

public import CORALean.ContDynamics.LinearSys.Operations.VerifySearch
public import CORALean.ContDynamics.LinearSys.Theorems.ConvexHullSupportCounterexampleSubsetReachSetExact
public import CORALean.ContDynamics.LinearSys.Theorems.NormLeOfMemInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactEq
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Instances
public import Mathlib.Analysis.Complex.Exponential
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# [1, Alg. 3 (termination)]: a safe, decidable instance on which `Alg. 3` never halts

`Alg. 3` halves `Δt` (line 15) only when `falsifiable = false` and `0 ∈ P̂`, the polytope of the
outer support vectors, but lines 19 and 23 choose the directions from `P̌`, the inner one's.

For `ẋ = x + u`, `X₀ = {0}`, `U = [-1, 1]`, `t = 1`, `R(1) ⊆ [-(e - 1), e - 1]`; `L = {c}`, with
`c` the order-`η` Taylor sum of `e - 1` plus `1/(η+1)!`, lies strictly between `e - 1` and the
upper bound of `Alg. 1` at `Δt = 1`, at distance `c - (e - 1) > 0` from `R(1)`. Every vertex of
`P̌` is left of the origin, so lines 19 and 23 return `ℓ₁ = +1` again, and every vertex of `P̂`
right of it: the safe exit, `0 ∈ P̌` and `0 ∈ P̂` all fail, and `verifySearch` answers
`undecided` for every `fuel`. This holds for every `η`, so for whichever one the tuning of
Sec. 5.1 picks, and for every sound support function oracle, support vectors and hull test.

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

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, Recenter (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- No list on one open side of a hyperplane through the origin has it in its hull. -/
theorem aux_inHull_false {inHull : List (Vec ℝ n) → Bool}
    (hhull : ∀ V, inHull V = true → (0 : Vec ℝ n) ∈ convexHull ℝ {v | v ∈ V})
    (φ : Vec ℝ n →ₗ[ℝ] ℝ) (V : List (Vec ℝ n)) (hV : (∀ v ∈ V, φ v < 0) ∨ ∀ v ∈ V, 0 < φ v) :
    inHull V = false := by -- --- PROOF ---
  by_contra h
  have h0 := hhull V (by simpa using h)
  rcases hV with hV | hV
  · have h1 : φ 0 < 0 := convexHull_min (fun v hv => hV v hv) (convex_halfSpace_lt φ.isLinear 0) h0
    simp at h1
  · have h1 : 0 < φ 0 := convexHull_min (fun v hv => hV v hv) (convex_halfSpace_gt φ.isLinear 0) h0
    simp at h1

/-- [1, Alg. 3 (search)] never exits while lines 19 and 23 keep returning `ℓ`, along which the
safe test fails and the outer and inner vertices lie on opposite sides of `φ = 0`. -/
theorem aux_verifySearchLoop_stall (sys : LinearSys 𝕋 n) (X₀ U : S n) (η : ℕ)
    (ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ) (ν₀ νU νL : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n)
    (νhat : ℝ → (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n) (ρL : (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ)
    {inHull : List (Vec ℝ n) → Bool}
    (hhull : ∀ V, inHull V = true → (0 : Vec ℝ n) ∈ convexHull ℝ {v | v ∈ V})
    {closestFacet : List (Vec ℝ n) → (Vec ℝ n →ₗ[ℝ] ℝ) × List ℕ}
    {gramSchmidt : List (Vec ℝ n) → (Vec ℝ n →ₗ[ℝ] ℝ)} (ℓ₁ : Vec ℝ n →ₗ[ℝ] ℝ)
    {φ ℓ : Vec ℝ n →ₗ[ℝ] ℝ} {Δt : ℝ} {k : ℕ}
    (hfacet : ∀ V : List (Vec ℝ n), V ≠ [] → (∀ v ∈ V, φ v < 0) → (closestFacet V).1 = ℓ)
    (hgs : ∀ V : List (Vec ℝ n), V ≠ [] → (∀ v ∈ V, φ v < 0) → gramSchmidt V = ℓ)
    (hsafe : 0 ≤ (sys.supportUpper Δt η X₀ U ρ ℓ k).ρR + ρL (-ℓ))
    (hhat : 0 < φ (νhat Δt ℓ - νL (-ℓ)))
    (hcheck : φ (sys.heldSim Δt (sys.supportCounterexample Δt ν₀ νU ℓ k).1
        (sys.supportCounterexample Δt ν₀ νU ℓ k).2 k - νL (-ℓ)) < 0)
    (fuel : ℕ) (s : LinearSys.VerifySearchState n) (hℓ : s.ℓ = ℓ) (hΔt : s.Δt = Δt)
    (hk : s.k = k) (hPhat : ∀ v ∈ s.Phat, 0 < φ v)
    (hPcheck : ∀ v ∈ s.Pcheck, φ v < 0) : -- --- STMT ---
    sys.verifySearchLoop X₀ U η ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt ℓ₁ fuel s
      = .undecided := by -- --- PROOF ---
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    obtain ⟨i, ℓ', Δt', k', Phat, Pcheck, f⟩ := s
    simp only at hℓ hΔt hk hPhat hPcheck
    subst hℓ hΔt hk
    -- the vertex lists after line 11 stay on their sides
    have hPc : ∀ v ∈ Pcheck ++ [sys.heldSim Δt' (sys.supportCounterexample Δt' ν₀ νU ℓ' k').1
        (sys.supportCounterexample Δt' ν₀ νU ℓ' k').2 k' - νL (-ℓ')], φ v < 0 := by
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact hPcheck v h
      · rw [List.mem_singleton.mp h]
        exact hcheck
    have hPh : ∀ v ∈ Phat ++ [νhat Δt' ℓ' - νL (-ℓ')], 0 < φ v := by
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact hPhat v h
      · rw [List.mem_singleton.mp h]
        exact hhat
    have hne : Pcheck ++ [sys.heldSim Δt' (sys.supportCounterexample Δt' ν₀ νU ℓ' k').1
        (sys.supportCounterexample Δt' ν₀ νU ℓ' k').2 k' - νL (-ℓ')] ≠ [] := by simp
    simp only [LinearSys.verifySearchLoop]
    rw [if_neg (not_lt.mpr hsafe), aux_inHull_false hhull φ _ (.inl hPc),
      aux_inHull_false hhull φ _ (.inr hPh)]
    simp only [Bool.false_eq_true, ↓reduceIte, and_false]
    split
    · -- line 19-21: the facet's normal is `ℓ` again, and its vertices a sublist
      refine ih _ (hfacet _ hne hPc) rfl rfl (fun v hv => ?_) (fun v hv => ?_)
      · obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp hv
        exact hPh v (List.mem_of_getElem? hj)
      · obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp hv
        exact hPc v (List.mem_of_getElem? hj)
    · -- line 23: the vector towards the origin is `ℓ` again
      exact ih _ (hgs _ hne hPc) rfl rfl hPh hPc


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 3 (termination)]: `R(1)` keeps a distance `c - (e - 1) > 0` from `L = {c}`, yet
`verifySearch` answers `undecided` for every `fuel`, `η` and sound oracle. -/
theorem LinearSys.verifySearch_stall_counterexample (η : ℕ) : -- --- STMT ---
    let sys : LinearSys ℝ 1 := LinearSys.canonical 1
    let X₀ : Zonotope (Vec ℝ 1) := Zonotope.ofPoint 0
    let U : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ => fun _ => 1⟩
    let c : ℝ := (∑ i ∈ Finset.range (η + 1), 1 / ((i + 1).factorial : ℝ)) +
      1 / ((η + 1).factorial : ℝ)
    let L : Set (Vec ℝ 1) := {fun _ => c}
    let ℓ₁ : Vec ℝ 1 →ₗ[ℝ] ℝ := LinearMap.proj 0
    -- decidable: `R(1)` and `L` are at a positive distance
    Real.exp 1 - 1 < c ∧
    (∀ x ∈ sys.reachSetExact (S := 𝒵) (Set.Icc 0 1) X₀ U 1, ∀ y ∈ L,
      c - (Real.exp 1 - 1) ≤ ‖x - y‖) ∧
    -- and yet, for every sound oracle, `Alg. 3` never exits
    ∀ (ρ : Zonotope (Vec ℝ 1) → (Vec ℝ 1 →ₗ[ℝ] ℝ) → ℝ)
      (_ : ∀ X : Zonotope (Vec ℝ 1), ∀ x ∈ construct X, ∀ d : Vec ℝ 1 →ₗ[ℝ] ℝ, d x ≤ ρ X d)
      (ν₀ νU νL : (Vec ℝ 1 →ₗ[ℝ] ℝ) → Vec ℝ 1) (_ : ∀ d, ν₀ d ∈ construct X₀)
      (_ : ∀ d, νU d ∈ construct U) (_ : ∀ d, νL d ∈ L)
      (ρL : (Vec ℝ 1 →ₗ[ℝ] ℝ) → ℝ) (_ : ∀ d, ∀ y ∈ L, d y ≤ ρL d)
      (νhat : ℝ → (Vec ℝ 1 →ₗ[ℝ] ℝ) → Vec ℝ 1)
      (_ : ℓ₁ (νhat 1 ℓ₁) = (sys.supportUpper (S := 𝒵) 1 η X₀ U ρ ℓ₁ 1).ρR)
      (inHull : List (Vec ℝ 1) → Bool)
      (_ : ∀ V, inHull V = true → (0 : Vec ℝ 1) ∈ convexHull ℝ {v | v ∈ V})
      (closestFacet : List (Vec ℝ 1) → (Vec ℝ 1 →ₗ[ℝ] ℝ) × List ℕ)
      (_ : ∀ V : List (Vec ℝ 1), V ≠ [] → (∀ v ∈ V, v 0 < 0) → (closestFacet V).1 = ℓ₁)
      (gramSchmidt : List (Vec ℝ 1) → (Vec ℝ 1 →ₗ[ℝ] ℝ))
      (_ : ∀ V : List (Vec ℝ 1), V ≠ [] → (∀ v ∈ V, v 0 < 0) → gramSchmidt V = ℓ₁)
      (fuel : ℕ),
      sys.verifySearch (S := 𝒵) X₀ U 1 η ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt fuel
        = .undecided := by -- --- PROOF ---
  intro sys X₀ U c L ℓ₁
  have hA : toRealMat sys.A = 1 := rfl
  have hnormA : ‖toRealMat sys.A‖ = 1 := by rw [hA]; exact norm_one
  have hUbdd : Bornology.IsBounded (construct U) := CompactSet.isBounded_construct U
  have hUnorm : ∀ u ∈ construct U, ‖u‖ ≤ 1 := by
    rintro u ⟨β, hβ, rfl⟩
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    simpa [U] using hβ 0
  -- `R(1)` lies left of `e - 1`
  have hR : ∀ x ∈ sys.reachSetExact (S := 𝒵) (Set.Icc 0 1) X₀ U 1, x 0 ≤ Real.exp 1 - 1 := by
    intro x hx
    rw [LinearSys.reachSetExact_eq (S := 𝒵) sys X₀ U zero_le_one hUbdd] at hx
    obtain ⟨a, ⟨z, hz, rfl⟩, v, hv, rfl⟩ := hx
    have hz0 : z = 0 := by
      obtain ⟨β, -, rfl⟩ := hz
      simp [X₀, Zonotope.ofPoint]
    have hvn := sys.norm_le_of_mem_inputReach (by rw [hnormA]; exact one_pos) zero_le_one
      hUnorm hv
    rw [hnormA] at hvn
    subst hz0
    have h0 : v 0 ≤ ‖v‖ := (le_abs_self _).trans (norm_le_pi_norm v 0)
    simp only [map_zero, zero_add]
    linarith [show (Real.exp (1 * 1) - 1) / 1 * 1 = Real.exp 1 - 1 by simp]
  -- `c` lies right of `e - 1`: the Taylor tail past order `η` is below `1/(η+1)!`
  have hF : (0 : ℝ) < ((η + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hexp : Real.exp 1 - 1 < c := by
    have h := Real.exp_bound' (x := 1) zero_le_one le_rfl (n := η + 2) (by omega)
    rw [Finset.sum_range_succ'] at h
    have hfac : ((η + 2).factorial : ℝ) = ((η : ℝ) + 2) * (η + 1).factorial := by
      rw [show η + 2 = (η + 1) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
    simp only [one_pow, Nat.factorial_zero, Nat.cast_one, div_one, hfac] at h
    have htail : ((η + 2 : ℕ) + 1 : ℝ) / (((η : ℝ) + 2) * (η + 1).factorial * (η + 2 : ℕ))
        < 1 / ((η + 1).factorial : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hF]
      push_cast
      nlinarith [hF]
    simp only [c]
    push_cast at h htail ⊢
    rw [one_mul] at h
    linarith
  -- the remainder of `P̂_U(Δt)` at `Δt = 1`: `ε = 1/(η+1)! · (1 - 1/(η+2))⁻¹ > 1/(η+1)!`
  let ε : ℝ := 1 * MatExp.expRemainderBound ((1 : ℝ) • toRealMat sys.A) η
  have hεval : ε = 1 / ((η + 1).factorial : ℝ) * (1 - 1 / ((η : ℝ) + 2))⁻¹ := by
    simp only [ε, MatExp.expRemainderBound, one_smul, hnormA, one_pow, one_mul]
  have hq : 0 < 1 - 1 / ((η : ℝ) + 2) := by
    rw [sub_pos, div_lt_one (by positivity)]
    linarith [(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]
  have hεc : 1 / ((η + 1).factorial : ℝ) < ε := by
    rw [hεval]
    refine lt_mul_of_one_lt_right (by positivity) ((one_lt_inv₀ hq).mpr ?_)
    have : (0 : ℝ) < 1 / ((η : ℝ) + 2) := by positivity
    linarith
  have hε0 : 0 ≤ ε := le_trans (by positivity) hεc.le
  -- a point of `P̂_U(Δt)`: the Taylor terms and the remainder at the input `1 ∈ U₀`
  let U₀ := Recenter.recenter U
  let w : Vec ℝ 1 := fun _ => 1
  have hw : w ∈ construct U₀ := by
    refine ⟨fun _ => 1, by simp, ?_⟩
    funext i
    simp [U₀, w, U, Recenter.recenter, Zonotope.recenter]
  -- the Taylor terms of `P̂_U(Δt)` at `w`
  have hmt : ∀ M : Mat ℝ 1 1,
      M *ᵥ w ∈ construct (Mtimes.mtimes (𝕄 := Mat ℝ) (S := 𝒵) M U₀) := fun M =>
    Mtimes.mtimes_outer (𝕄 := Mat ℝ) (S := 𝒵) M U₀
      (Set.mem_biUnion (x := M) (by simp) ⟨w, hw, rfl⟩)
  have htay : ∀ j : ℕ, (∑ i ∈ Finset.range (j + 1), sys.inputTerm 1 i *ᵥ w) ∈
      construct (sys.inputTaylorSum (S := 𝒵) 1 U₀ j) := by
    intro j
    induction j with
    | zero =>
      rw [Finset.sum_range_one]
      exact hmt _
    | succ j ih =>
      rw [Finset.sum_range_succ]
      exact Plus.plus_outer _ _ (Set.add_mem_add ih (hmt _))
  -- the remainder term holds the constant matrix `ε`, and so the point reaches `Σ + ε`
  let Mε : Mat ℝ 1 1 := fun _ _ => ε
  have hM : Mε ∈ construct (MatExp.inputRemainder (toRealMat sys.A) 1 η) :=
    fun p => ⟨by simp only [Entrywise.entry_mat, MatExp.inputRemainder, Mε]; linarith, le_rfl⟩
  have hxp : (∑ i ∈ Finset.range (η + 1), sys.inputTerm 1 i *ᵥ w) + Mε *ᵥ w ∈
      construct (sys.inputSolution (S := 𝒵) 1 η U₀) :=
    Plus.plus_outer _ _ (Set.add_mem_add (htay η) (Mtimes.mtimes_outer (𝕄 := ℐ) (S := 𝒵)
      (MatExp.inputRemainder (toRealMat sys.A) 1 η) U₀
      (Set.mem_biUnion (x := Mε) hM ⟨w, hw, rfl⟩)))
  have hxp0 : ((∑ i ∈ Finset.range (η + 1), sys.inputTerm 1 i *ᵥ w) + Mε *ᵥ w) 0 =
      (∑ i ∈ Finset.range (η + 1), 1 / ((i + 1).factorial : ℝ)) + ε := by
    simp [LinearSys.inputTerm, Finset.sum_apply, Matrix.mulVec, dotProduct, Mε, w, hA]
  refine ⟨hexp, ?_, ?_⟩
  · -- the distance between `R(1)` and `L`
    intro x hx y hy
    rw [Set.mem_singleton_iff.mp hy]
    have h1 := hR x hx
    have h2 : |x 0 - c| ≤ ‖x - (fun _ => c : Vec ℝ 1)‖ :=
      calc |x 0 - c| = ‖(x - (fun _ => c : Vec ℝ 1)) 0‖ := by rw [Real.norm_eq_abs]; rfl
        _ ≤ _ := norm_le_pi_norm _ 0
    linarith [neg_abs_le (x 0 - c)]
  intro ρ hρ ν₀ νU νL hν₀ hνU hνL ρL hρL νhat hνhat inHull hhull closestFacet hfacet
    gramSchmidt hgs fuel
  have hup : (∑ i ∈ Finset.range (η + 1), 1 / ((i + 1).factorial : ℝ)) + ε ≤
      (sys.supportUpper (S := 𝒵) 1 η X₀ U ρ ℓ₁ 1).ρR := by
    -- line 12 at `k = 1`: `ρ(X₀, d₁) + ℓ₁(P_u(t₁)) + ρ(P̂_U(Δt), ℓ₁)`, the middle term `0`
    simp only [LinearSys.supportUpper]
    have h0X : (0 : Vec ℝ 1) ∈ construct X₀ := OfPoint.mem_ofPoint (0 : Vec ℝ 1)
    have h1 := hρ X₀ 0 h0X (ℓ₁ ∘ₗ (exp ((1 : ℝ) • toRealMat sys.A)).mulVecLin)
    have h3 := hρ _ _ hxp ℓ₁
    have hc : Recenter.center U = 0 := rfl
    rw [hc, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero, map_zero, add_zero, zero_add]
    rw [map_zero] at h1
    have h4 : ℓ₁ ((∑ i ∈ Finset.range (η + 1), sys.inputTerm 1 i *ᵥ w) + Mε *ᵥ w) =
        (∑ i ∈ Finset.range (η + 1), 1 / ((i + 1).factorial : ℝ)) + ε := hxp0
    linarith
  -- the three facts the loop reads, along `ℓ₁` at `Δt = 1`, `k = 1`
  have hL : νL (-ℓ₁) = fun _ => c := Set.mem_singleton_iff.mp (hνL _)
  have hsafe : 0 ≤ (sys.supportUpper (S := 𝒵) 1 η X₀ U ρ ℓ₁ 1).ρR + ρL (-ℓ₁) := by
    have := hρL (-ℓ₁) (fun _ => c) rfl
    simp only [LinearMap.neg_apply, ℓ₁, LinearMap.proj_apply] at this
    linarith
  have hhat : 0 < ℓ₁ (νhat 1 ℓ₁ - νL (-ℓ₁)) := by
    rw [map_sub, hνhat, hL]
    simp only [ℓ₁, LinearMap.proj_apply]
    linarith
  have hcheck : ℓ₁ (sys.heldSim 1 (sys.supportCounterexample 1 ν₀ νU ℓ₁ 1).1
      (sys.supportCounterexample 1 ν₀ νU ℓ₁ 1).2 1 - νL (-ℓ₁)) < 0 := by
    have hmem := sys.convexHull_supportCounterexample_subset_reachSetExact (S := 𝒵) X₀ U
      (ConvexSet.convex_construct X₀) (ConvexSet.convex_construct U) hUbdd one_pos hν₀ hνU
      (fun _ : Unit => ℓ₁) 1 (subset_convexHull ℝ _ ⟨(), rfl⟩)
    rw [Nat.cast_one, one_mul] at hmem
    have := hR _ hmem
    rw [map_sub, hL]
    simp only [ℓ₁, LinearMap.proj_apply]
    linarith
  -- line 1's `ℓ₁ = I_n(·,1)` is the first coordinate
  have hℓ : (∑ j : Fin 1, if (j : ℕ) = 0 then (LinearMap.proj j : Vec ℝ 1 →ₗ[ℝ] ℝ) else 0)
      = ℓ₁ := by
    simp [ℓ₁]
  simp only [LinearSys.verifySearch]
  rw [hℓ]
  exact aux_verifySearchLoop_stall (S := 𝒵) sys X₀ U η ρ ν₀ νU νL νhat ρL hhull ℓ₁ (φ := ℓ₁)
    (Δt := 1) (k := 1) hfacet hgs hsafe hhat hcheck fuel ⟨1, ℓ₁, 1, 1, [], [], true⟩ rfl rfl rfl
    (fun v hv => by simp at hv) (fun v hv => by simp at hv)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
