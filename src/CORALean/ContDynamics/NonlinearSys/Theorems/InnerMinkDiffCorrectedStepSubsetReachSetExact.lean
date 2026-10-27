module

public import CORALean.ContDynamics.NonlinearSys.Definitions.IsInnerMinkDiffCorrectedCert
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffCorrectedStep
public import CORALean.ContDynamics.NonlinearSys.Theorems.MinkowskiDiffAddSubsetReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Theorems.MinkowskiDiffConvexHullBallSubsetReachSetExact

@[expose] public section

/-!
# One step of the corrected inner algorithm stays inside the reachable sets

Lines 15 and 16 of the corrected [1, Alg. 1] from a convex `X = R̂(t_k)`: `R̂(t_{k+1})` holds only
states some run from `X` reaches at `Δt` (`Prop. 1`, `minkowskiDiff_add_subset_reachSetExact`),
`R̂(τ_k)` only states one reaches at some `t ∈ [0, Δt]` (the repaired `Prop. 2`,
`minkowskiDiff_convexHull_ball_subset_reachSetExact`), and `R̂(t_{k+1})` is convex again, so the
next step may erode its hull too. `R̂_err` symmetric about `0` and about `cen(R̂_err)` makes that
center `0`, so `R̂(t_{k+1}) ⊖ C` is `(R_aff ⊖ R̂_err) ⊖ C`, the set the repaired `Prop. 2` erodes.
The input is the constant `u₀`, the autonomous system (4) of [1].

## Inputs
* `ops` – set operations
* `zono` – zonotope of a set's center and generators
* `sys` – system
* `u₀` – constant input
* `Δt` – step size
* `μ` – enlargement factor
* `fuel` – bound per remainder loop
* `X` – start set

## Hypotheses
* `hΔt` – step size positive
* `hX` – start set convex

## Conclusion
* the next time-point set and the time-interval set lie in the exact reachable sets, the former
  convex

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix NormedSpace Pointwise Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ} {𝓛 : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A bounded nonempty set symmetric about `0` and about `a` has `a = 0`: the two symmetries
compose to the translation by `2a`, which a bounded set only survives at `a = 0`. -/
private theorem NonlinearSys.aux_center_eq_zero {S : Set (Vec ℝ n)} (hS : Bornology.IsBounded S)
    (hne : S.Nonempty) (h0 : ∀ e ∈ S, -e ∈ S) {a : Vec ℝ n}
    (ha : ∀ e ∈ S, (2 : ℝ) • a - e ∈ S) : -- --- CONCL ---
    a = 0 := by -- --- PROOF ---
  obtain ⟨e, he⟩ := hne
  -- every `e + k • (2a)` stays in `S`
  have hk : ∀ k : ℕ, e + (k : ℝ) • ((2 : ℝ) • a) ∈ S := by
    intro k
    induction k with
    | zero => simpa using he
    | succ k ih =>
      have h := ha _ (h0 _ ih)
      convert h using 1
      push_cast
      rw [add_smul, one_smul]
      abel
  -- a ball of radius `R` holds them all, so `k‖2a‖ ≤ R + ‖e‖` for every `k`
  obtain ⟨R, hR⟩ := hS.subset_closedBall 0
  by_contra hne0
  have hpos : 0 < ‖(2 : ℝ) • a‖ := norm_pos_iff.mpr (smul_ne_zero two_ne_zero hne0)
  obtain ⟨k, hk'⟩ := exists_nat_gt ((R + ‖e‖) / ‖(2 : ℝ) • a‖)
  have h1 := hR (hk k)
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : ‖(k : ℝ) • ((2 : ℝ) • a)‖ ≤ ‖e + (k : ℝ) • ((2 : ℝ) • a)‖ + ‖e‖ := by
    have := norm_sub_le (e + (k : ℝ) • ((2 : ℝ) • a)) e
    rwa [add_sub_cancel_left] at this
  rw [norm_smul, Real.norm_natCast] at h2
  rw [div_lt_iff₀ hpos] at hk'
  linarith

/-- A Minkowski difference from a convex set is convex. -/
private theorem NonlinearSys.aux_convex_minkowskiDiff' {A B : Set (Vec ℝ n)} (hA : Convex ℝ A) :
    Convex ℝ (minkowskiDiff A B) := by
  intro x hx z hz a b ha hb hab e he
  have h := hA (hx e he) (hz e he) ha hb hab
  convert h using 1
  rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The corrected [1, Alg. 1], lines 15-16, from a convex `X`: `R̂(t_{k+1}) ⊆ R(Δt)`,
`R̂(τ_k) ⊆ ⋃_{t ∈ [0, Δt]} R(t)` and `R̂(t_{k+1})` convex, given the step's certificate. -/
theorem NonlinearSys.innerMinkDiffCorrectedStep_subset_reachSetExact
    (ops : NonlinearSys.InnerMinkDiffOps n 𝓛) (zono : Set (Vec ℝ n) → Real.Zonotope (Vec ℝ n))
    (sys : NonlinearSys n m) (u₀ : Vec ℝ m) {Δt : ℝ} (hΔt : 0 < Δt) (μ : ℝ) (fuel : ℕ)
    {X : Set (Vec ℝ n)} (hX : Convex ℝ X) : -- --- CONCL ---
    ∀ st ∈ NonlinearSys.innerMinkDiffCorrectedStep ops zono (fun x => sys.f x u₀) Δt μ fuel X,
      NonlinearSys.IsInnerMinkDiffCorrectedCert sys u₀ Δt ops zono X st →
      st.Rtk1 ⊆ sys.reachSetExact (S := 𝒮) (Icc 0 Δt) X {u₀} Δt ∧
      st.Rtauk ⊆ ⋃ t ∈ Icc 0 Δt, sys.reachSetExact (S := 𝒮) (Icc 0 t) X {u₀} t ∧
      Convex ℝ st.Rtk1 := by -- --- PROOF ---
  intro st (h : NonlinearSys.innerMinkDiffCorrectedStep ops zono (fun x => sys.f x u₀) Δt μ fuel X
    = some st) cert
  -- what lines 7-8, 14-16 computed
  have hst : st.Raff = (fun x => x + st.Rcon) ''
        ((fun x => st.xstar + exp (Δt • st.A) *ᵥ (x - st.xstar)) '' X) ∧
      st.c = ops.cen st.C + ops.cen st.Rerr ∧
      st.Rtk1 = (fun x => x + (2 : ℝ) • ops.cen st.Rerr) '' minkowskiDiff st.Raff st.Rerr ∧
      st.Rtauk = (fun x => x + (2 : ℝ) • st.c) '' minkowskiDiff
        (convexHull ℝ (minkowskiDiff (minkowskiDiff X st.Rerr) st.C ∪ minkowskiDiff st.Rtk1 st.C))
        {y | ‖y‖₂ ≤ Real.sqrt (zono X).h *
          genOpNorm₂ fun j => (exp (Δt • st.A) - 1) *ᵥ (zono X).G j} := by
    unfold NonlinearSys.innerMinkDiffCorrectedStep at h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, rfl, rfl, rfl⟩
  set M := exp (Δt • st.A)
  set v := st.xstar - M *ᵥ st.xstar + st.Rcon
  have hMv : ∀ x₀, M *ᵥ x₀ + v = st.xstar + M *ᵥ (x₀ - st.xstar) + st.Rcon := fun x₀ => by
    simp only [v, Matrix.mulVec_sub]
    abel
  have hRaff : st.Raff = (fun x₀ => M *ᵥ x₀ + v) '' X := by
    rw [hst.1, image_image]
    exact image_congr fun x _ => by rw [hMv]
  have hM : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  -- `cen(R̂_err) = 0`: `R̂_err` is symmetric about both
  have hcen : ops.cen st.Rerr = 0 :=
    aux_center_eq_zero cert.compact.isBounded cert.nonempty cert.symm cert.cen
  have hRtk1 : st.Rtk1 = minkowskiDiff st.Raff st.Rerr := by
    rw [hst.2.2.1, hcen, smul_zero]
    simp only [add_zero, image_id']
  obtain ⟨Ω, K, hLip, hex⟩ := cert.flow
  refine ⟨?_, ?_, ?_⟩
  · -- line 15 by `Prop. 1`, (21) rewritten about `x*`
    rw [hst.2.2.1, hRaff]
    refine NonlinearSys.minkowskiDiff_add_subset_reachSetExact (S := 𝒮) sys X {u₀} hΔt.le M hM v
      cert.compact cert.convex cert.nonempty cert.cen (mem_singleton u₀) hLip hex
      fun x₀ hx₀ x hx0 hder => ?_
    rw [hMv]
    exact cert.err x₀ hx₀ x hx0 hder
  · -- line 16 by the repaired `Prop. 2`, the two differences reordered
    have hswap : minkowskiDiff (minkowskiDiff X st.Rerr) st.C =
        minkowskiDiff (minkowskiDiff X st.C) st.Rerr := by
      rw [← minkowskiDiff_add_assoc, ← minkowskiDiff_add_assoc, add_comm]
    rw [hst.2.2.2, hswap, hRtk1, hRaff]
    refine NonlinearSys.minkowskiDiff_convexHull_ball_subset_reachSetExact sys hX (zono X)
      cert.zono {u₀} hΔt M hM v st.C st.Rerr cert.compactE cert.convexE
      (cert.nonemptyC.add cert.nonempty) cert.symmE (mem_singleton u₀) hLip hex
      fun t ht x₀ hx₀ x hx0 hder => ?_
    rw [hMv]
    exact cert.errτ t ht x₀ hx₀ x hx0 hder
  · -- `R_aff` is an affine image of `X`, and `⊖` keeps convexity
    rw [hRtk1, hRaff]
    clear_value M v
    refine aux_convex_minkowskiDiff' ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩ a b ha hb hab
    refine ⟨a • x + b • z, hX hx hz ha hb hab, ?_⟩
    show M *ᵥ (a • x + b • z) + v = a • (M *ᵥ x + v) + b • (M *ᵥ z + v)
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_add, smul_add,
      add_add_add_comm, ← add_smul, hab, one_smul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
