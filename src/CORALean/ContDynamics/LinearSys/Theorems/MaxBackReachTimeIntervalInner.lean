module

public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetExistsForall
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachTimeInterval
public import CORALean.ContDynamics.LinearSys.Theorems.BackReachSetExistsForallEq
public import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombInner
public import CORALean.ContSet.ConZonotope.Real.Theorems.Basic
public import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.ContSet.Theorems.SegmentsMinkowskiDiffSubset
public import CORALean.ContSet.HPolytope.Real.Theorems.MinkDiffOfInner
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

@[expose] public section

/-!
# `Thm. 2`: what `Alg. 3` returns is inside the EA set over `τ`

[1, Thm. 2] holds [1, Alg. 3] to its claim, and it runs `⊆`, not `⊇`: (54) is an
*inner* approximation. Proved outright: line 12's linear map and `⊕ -Z̲_U(t_k)`,
line 11's hull and conversion, `Lemma 1` carrying the hull of two erosions into
the erosion of the hull — the step the lemma exists for — the time-point
identity `Prop. 5` in its inner direction, `Prop. 2`, and line 14's union.

`hhom` and `hZU` are what the paper imports: (21)'s inner homogeneous
time-interval solution and (25)-(29)'s particular solutions. Both are stated
*per time* `t ∈ τ_k`. The paper's own proof states them against the union over
`τ_k` and then erodes that union, which needs `(⋃ₜ Aₜ) ⊖ B ⊆ ⋃ₜ (Aₜ ⊖ B)` — the
direction that fails; see the findings on the paper's page.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c}
variable {P₁ P₂ : HPolytope (Vec ℝ n)} {Uz W₀ ZW : Zonotope (Vec ℝ n)}
variable {Zw : ℝ → Zonotope (Vec ℝ n)} {Δt : ℝ} {η : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The `k`-th iteration starts at `t_k = t₀ + k Δt`, line 7 read off the
recursion. -/
theorem LinearSys.aux_maxBackReachRun_t (sys : LinearSys 𝕋 n) (t₀ : ℝ) (k : ℕ) :
    (sys.maxBackReachRun ρ P₁ P₂ Uz W₀ Zw t₀ Δt η k).t = t₀ + k * Δt := by -- --- PROOF ---
  induction k with
  | zero => simp [LinearSys.maxBackReachRun, LinearSys.maxBackReachInit]
  | succ k ih =>
      simp only [LinearSys.maxBackReachRun, LinearSys.maxBackReachStep, ih]
      push_cast
      ring

/-- [1, Prop. 2] for `R^{∃∀}`, over runs whose domain reaches `t_end`: the
input found for time `t` is extended past `t` by a constant, which superposition
shows changes nothing at `t`. -/
theorem LinearSys.aux_backReach_subset_timeInterval (sys : LinearSys 𝕋 n) {U W Xend : S n}
    {tend t : ℝ} (ht : 0 ≤ t) (hle : t ≤ tend) {τ : Set ℝ} (hτ : t ∈ τ)
    (hU : Bornology.IsBounded (construct U)) (hW : Bornology.IsBounded (construct W))
    {c : Vec ℝ n} (hc : c ∈ construct U) :
    sys.backReachSetExistsForall (Set.Icc 0 t) U W Xend t ⊆
      sys.timeIntervalBackReachSetExistsForall
        (Set.Icc 0 tend) U W Xend τ := by -- --- PROOF ---
  classical
  rintro x₀ ⟨u, hu, humeas, hall⟩
  have hsub : Set.Icc (0:ℝ) t ⊆ Set.Icc (0:ℝ) tend := Set.Icc_subset_Icc le_rfl hle
  -- the shorter domain's restriction of the longer one is the shorter one
  have hres : (volume.restrict (Set.Icc (0:ℝ) tend)).restrict (Set.Icc (0:ℝ) t)
      = volume.restrict (Set.Icc (0:ℝ) t) := by
    rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_self_of_subset_left hsub]
  set u' : ℝ → Vec ℝ n := Set.piecewise (Set.Icc (0:ℝ) t) u (fun _ => c) with hu'def
  have hu'adm : ∀ s ∈ Set.Icc (0:ℝ) tend, u' s ∈ construct U := by
    intro s _
    by_cases h : s ∈ Set.Icc (0:ℝ) t
    · rw [hu'def, Set.piecewise_eq_of_mem _ _ _ h]; exact hu s h
    · rw [hu'def, Set.piecewise_eq_of_notMem _ _ _ h]; exact hc
  have hu'meas : AEStronglyMeasurable u' (volume.restrict (Set.Icc (0:ℝ) tend)) :=
    AEStronglyMeasurable.piecewise measurableSet_Icc (hres ▸ humeas) aestronglyMeasurable_const
  refine ⟨u', hu'adm, hu'meas, fun w hw hwmeas => ?_⟩
  -- the disturbance restricts to the shorter domain, where the witness lives
  obtain ⟨x, traj, hx0, hxt⟩ := hall w (fun s hs => hw s (hsub hs)) (hres ▸ hwmeas.restrict)
  have hsup := traj.superposition ht hU hW
  rw [hx0] at hsup
  have hint : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u' s)
      = ∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht] at hs
    rw [hu'def, Set.piecewise_eq_of_mem _ _ _ hs]
  refine ⟨fun r => sys.closedForm x₀ u' r + sys.closedForm 0 w r,
    sys.perturbedTrajectory_closedForm (le_trans ht hle) hU hW x₀ hu'adm hu'meas hw hwmeas,
    by simp only [LinearSys.closedForm_zero, add_zero], t, hτ, ?_⟩
  -- the two runs agree at `t`, since `u'` agrees with `u` there
  have hend : sys.closedForm x₀ u' t + sys.closedForm 0 w t = x t := by
    rw [hsup]
    simp only [LinearSys.closedForm, hint, Matrix.mulVec_zero, zero_add]
  show sys.closedForm x₀ u' t + sys.closedForm 0 w t ∈ construct Xend
  rw [hend]
  exact hxt

/-- One iteration of [1, Alg. 3] lands inside the time-point solutions over
`τ_k`, which is (54). -/
theorem LinearSys.aux_maxBackReachStep_inner (sys : LinearSys 𝕋 n) {U W Xend : S n}
    {s : LinearSys.MaxBackReachState n} (hs : 0 ≤ s.t)
    (hZW : (sys.maxBackReachStep ρ P₁ P₂ Uz W₀ Zw Δt η s).ZW = ZW)
    (hU : Bornology.IsBounded (construct U)) (hW : Bornology.IsBounded (construct W))
    (hker₁ : ∀ (i : Fin P₁.me) (y : Vec ℝ n), P₁.Ae i y = 0)
    (hker₂ : ∀ (i : Fin P₂.me) (y : Vec ℝ n), P₂.Ae i y = 0)
    (hne₁ : (LinearSys.maxBackReachCZ ρ P₁ ZW).construct.Nonempty)
    (hne₂ : (LinearSys.maxBackReachCZ ρ P₂ ZW).construct.Nonempty)
    (hhom : ∀ y ∈ minkowskiDiff (segments P₁.construct P₂.construct) ZW.construct,
      ∃ t ∈ Set.Icc s.t (s.t + Δt), y ∈ (exp ((s.t + Δt - t) • toRealMat sys.A)).mulVecLin ''
        minkowskiDiff (construct Xend) (sys.inputReach W t))
    (hZU : ∀ t ∈ Set.Icc s.t (s.t + Δt), s.ZU.construct ⊆
      (exp ((s.t + Δt - t) • toRealMat sys.A)).mulVecLin '' sys.inputReach U t) :
    (sys.maxBackReachStep ρ P₁ P₂ Uz W₀ Zw Δt η s).R.construct ⊆
      ⋃ t ∈ Set.Icc s.t (s.t + Δt),
        sys.backReachSetExistsForall (Set.Icc 0 t) U W Xend t := by -- --- PROOF ---
  -- line 12: the map, the hull and the input summand, spelled out
  have hR : (sys.maxBackReachStep ρ P₁ P₂ Uz W₀ Zw Δt η s).R
      = ConZonotope.mtimes (exp ((-(s.t + Δt)) • toRealMat sys.A))
        (ConZonotope.plus
          (ConZonotope.linComb (LinearSys.maxBackReachCZ ρ P₁ ZW)
            (LinearSys.maxBackReachCZ ρ P₂ ZW))
          (Zonotope.conZonotope (Zonotope.mtimes (-(1 : Mat ℝ n n)) s.ZU))) := by
    rw [← hZW]
    rfl
  rw [hR, ← ConZonotope.mtimes_exact, ← ConZonotope.plus_exact, ← Zonotope.conZonotope_exact,
    ← Zonotope.mtimes_exact]
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hv
  obtain ⟨c, hc, rfl⟩ := hz
  -- lines 11, Alg. 1, (11): each endpoint of the hull is a `P_i` eroded by `Ẑ_W(τ_k)`
  have hsub : ∀ P : HPolytope (Vec ℝ n), (∀ (i : Fin P.me) (w : Vec ℝ n), P.Ae i w = 0) →
      (LinearSys.maxBackReachCZ ρ P ZW).construct ⊆ minkowskiDiff P.construct ZW.construct := by
    intro P hker
    have heq : (LinearSys.maxBackReachCZ ρ P ZW).construct
        = (P.minkDiffOf ZW.construct fun i => ZW.supportBound (P.A i)).construct :=
      HPolytope.conZonotope_exact _ _
    rw [heq]
    exact HPolytope.minkDiffOf_inner _ _ _ fun i w _ => hker i w
  -- [1, Lemma 1]: the hull of the two erosions is inside the erosion of the hull
  have hL : y ∈ minkowskiDiff (segments P₁.construct P₂.construct) ZW.construct := by
    obtain ⟨y₁, h₁, y₂, h₂, lam, hlam, rfl⟩ := ConZonotope.linComb_inner _ _ hne₁ hne₂ hy
    exact segments_minkowskiDiff_subset _ _ _
      ⟨y₁, hsub P₁ hker₁ h₁, y₂, hsub P₂ hker₂ h₂, lam, hlam, rfl⟩
  -- (21): the eroded hull is covered slice by slice, and `t` names the slice
  obtain ⟨t, ht, w', hw', hw'eq⟩ := hhom y hL
  obtain ⟨d, hd, hdeq⟩ := hZU t ht hc
  have ht0 : 0 ≤ t := le_trans hs ht.1
  refine Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩
  rw [sys.backReachSetExistsForall_eq U W Xend ht0 hU hW]
  refine ⟨w' + -d, ⟨w', hw', -d, by rw [Set.mem_neg, neg_neg]; exact hd, rfl⟩, ?_⟩
  -- the two exponentials compose to `e^{-At}`, which is [1, Prop. 5]'s map
  have hcomm : Commute ((-(s.t + Δt)) • toRealMat sys.A) ((s.t + Δt - t) • toRealMat sys.A) :=
    ((Commute.refl _).smul_left _).smul_right _
  have hexp : exp ((-(s.t + Δt)) • toRealMat sys.A) * exp ((s.t + Δt - t) • toRealMat sys.A)
      = exp ((-t) • toRealMat sys.A) := by
    have hadd : (-(s.t + Δt)) • toRealMat sys.A + (s.t + Δt - t) • toRealMat sys.A
        = (-t) • toRealMat sys.A := by
      rw [← add_smul]; congr 1; ring
    rw [← hadd]
    exact (exp_add_of_commute hcomm).symm
  rw [← hw'eq, ← hdeq]
  show exp ((-t) • toRealMat sys.A) *ᵥ (w' + -d)
    = exp ((-(s.t + Δt)) • toRealMat sys.A) *ᵥ
        (exp ((s.t + Δt - t) • toRealMat sys.A) *ᵥ w'
          + (-(1 : Mat ℝ n n)) *ᵥ (exp ((s.t + Δt - t) • toRealMat sys.A) *ᵥ d))
  rw [Matrix.neg_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_neg, ← Matrix.mulVec_add,
    Matrix.mulVec_mulVec, hexp]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: what `Alg. 3` returns is inside the time-interval EA
backward reachable set — an inner approximation, `⊆`. -/
theorem LinearSys.maxBackReachTimeInterval_inner (sys : LinearSys 𝕋 n) {U W Xend : S n}
    {t₀ tend : ℝ} {ω : ℕ} {τ : Set ℝ} {st : ℕ → LinearSys.MaxBackReachState n}
    (hΔt : Δt = (tend - t₀) / ω) (ht₀ : 0 ≤ t₀) (hΔt0 : 0 ≤ Δt)
    (hst : ∀ k, st k = sys.maxBackReachRun ρ P₁ P₂ Uz W₀ Zw t₀ Δt η k)
    (hτ : Set.Icc t₀ tend ⊆ τ) (hlast : t₀ + ω * Δt ≤ tend)
    (hU : Bornology.IsBounded (construct U)) (hW : Bornology.IsBounded (construct W))
    {c : Vec ℝ n} (hc : c ∈ construct U)
    -- no equality rows: [1, Def. 2]'s target set is a `⟨H,d⟩_H`
    (hker₁ : ∀ (i : Fin P₁.me) (y : Vec ℝ n), P₁.Ae i y = 0)
    (hker₂ : ∀ (i : Fin P₂.me) (y : Vec ℝ n), P₂.Ae i y = 0)
    -- [1, Lemma 1] asks for nonempty sets, and so does the hull of line 11
    (hne₁ : ∀ k < ω, (LinearSys.maxBackReachCZ ρ P₁ (st (k + 1)).ZW).construct.Nonempty)
    (hne₂ : ∀ k < ω, (LinearSys.maxBackReachCZ ρ P₂ (st (k + 1)).ZW).construct.Nonempty)
    -- (21): the hull of `P₁`, `P₂` eroded by `Ẑ_W(τ_k)`, covered slice by slice
    (hhom : ∀ k < ω, ∀ y ∈ minkowskiDiff (segments P₁.construct P₂.construct)
        (st (k + 1)).ZW.construct,
      ∃ t ∈ Set.Icc (st k).t ((st k).t + Δt),
        y ∈ (exp (((st k).t + Δt - t) • toRealMat sys.A)).mulVecLin ''
          minkowskiDiff (construct Xend) (sys.inputReach W t))
    -- (25)-(29): the inner input particular solution, carried to `t_{k+1}`
    (hZU : ∀ k < ω, ∀ t ∈ Set.Icc (st k).t ((st k).t + Δt), (st k).ZU.construct ⊆
      (exp (((st k).t + Δt - t) • toRealMat sys.A)).mulVecLin '' sys.inputReach U t) :
    sys.maxBackReachTimeInterval ρ P₁ P₂ Uz W₀ Zw t₀ tend η ω ⊆
      sys.timeIntervalBackReachSetExistsForall
        (Set.Icc 0 tend) U W Xend τ := by -- --- PROOF ---
  subst hΔt
  intro x hx
  -- line 14: `x` comes from one of the `ω` iterations
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hx
  have hstep : sys.maxBackReachStep ρ P₁ P₂ Uz W₀ Zw ((tend - t₀) / ω) η (st k) = st (k + 1) := by
    rw [hst k, hst (k + 1)]
    rfl
  rw [← hst (k + 1), ← hstep] at hxk
  have hZW := congrArg LinearSys.MaxBackReachState.ZW hstep
  -- line 7: the `k`-th iteration covers `τ_k = [t₀ + kΔt, t₀ + (k+1)Δt]`
  have htk : (st k).t = t₀ + k * ((tend - t₀) / ω) := by
    rw [hst k]; exact sys.aux_maxBackReachRun_t t₀ k
  have hs0 : 0 ≤ (st k).t := by
    rw [htk]
    have : 0 ≤ (k : ℝ) * ((tend - t₀) / ω) := mul_nonneg (Nat.cast_nonneg k) hΔt0
    linarith
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (sys.aux_maxBackReachStep_inner hs0 hZW hU hW
    hker₁ hker₂ (hne₁ k hk) (hne₂ k hk) (hhom k hk) (hZU k hk) hxk)
  -- `τ_k ⊆ τ ⊆ [t₀, t_end]`, so [1, Prop. 2] carries the time-point solution over
  have hkω : (k : ℝ) + 1 ≤ ω := by exact_mod_cast hk
  have hup : t ≤ tend := by
    have h1 : t ≤ t₀ + ((k : ℝ) + 1) * ((tend - t₀) / ω) := by rw [htk] at ht; linarith [ht.2]
    have h2 : ((k : ℝ) + 1) * ((tend - t₀) / ω) ≤ (ω : ℝ) * ((tend - t₀) / ω) :=
      mul_le_mul_of_nonneg_right hkω hΔt0
    linarith
  have hlo : t₀ ≤ t := by rw [htk] at ht; nlinarith [ht.1, Nat.cast_nonneg (α := ℝ) k]
  exact sys.aux_backReach_subset_timeInterval (le_trans hs0 ht.1) hup (hτ ⟨hlo, hup⟩) hU hW hc hxt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
