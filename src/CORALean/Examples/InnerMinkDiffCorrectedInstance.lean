import CORALean.ContDynamics.NonlinearSys.Theorems.InnerMinkDiffCorrectedSubsetReachSetExact

/-!
# The corrected inner algorithm's hypotheses hold on an instance

`NonlinearSys.innerMinkDiffCorrected_subset_reachSetExact`, the corrected [1, Alg. 1], asks a
certificate of every step of the run. On `ẋ = 0` from `X₀ = [0, 1]`, one step over `[0, 1]`,
with error sets `{0}` and the zonotope `⟨1/2, 1/2⟩` of `X₀` as `zono`, every step has it, so the
theorem applies, and the run returns a set holding `1/2`, which the theorem places in the
reachable set.

## Inputs
* none

## Output
* the certificates of the run, and a nonempty output the theorem bounds

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Pointwise Set


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open scoped Matrix.Norms.L2Operator

/-- The generator norm of zero generators is `0`. -/
private theorem IMD.aux_genOpNorm₂_zero {h n : ℕ} : -- --- CONCL ---
    genOpNorm₂ (fun _ : Fin h => (0 : Vec ℝ n)) = 0 := by -- --- PROOF ---
  unfold genOpNorm₂
  have h0 : (Matrix.of fun i j => (fun _ : Fin h => (0 : Vec ℝ n)) j i : Mat ℝ n h) = 0 := by
    ext i j
    simp
  rw [h0]
  exact norm_zero

end

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system `ẋ = 0` on the line, its output the state. -/
def IMD.sys : NonlinearSys 1 1 := ⟨fun _ _ => 0, 1, fun x _ => x⟩

/-- The subroutines of the inner algorithm for `ẋ = 0`: zero Jacobian, error sets `{0}`,
center `0`. -/
def IMD.ops : NonlinearSys.InnerMinkDiffOps 1 Unit :=
  ⟨fun _ => 0, id, fun _ => 0, fun _ _ _ _ => {0}, fun _ _ _ => {0}, fun _ _ => (), (),
    fun _ _ => (), fun _ _ => true⟩

/-- The initial set `[0, 1]`. -/
def IMD.X₀ : Set (Vec ℝ 1) := {x | 0 ≤ x 0 ∧ x 0 ≤ 1}

/-- The zonotope `⟨1/2, 1/2⟩`, which is `[0, 1]`. -/
noncomputable def IMD.Z : Real.Zonotope (Vec ℝ 1) := ⟨1, fun _ => 1 / 2, fun _ _ => 1 / 2⟩

/-- Every step of `ẋ = 0` from a subset of `[0, 1]` has its certificate. -/
theorem IMD.cert {Δt : ℝ} (hΔt : 0 < Δt) (μ : ℝ) {X : Set (Vec ℝ 1)} (hX : X ⊆ IMD.X₀)
    (st : NonlinearSys.InnerMinkDiffState 1 Unit)
    (h : NonlinearSys.innerMinkDiffCorrectedStep IMD.ops (fun _ => IMD.Z)
      (fun x => IMD.sys.f x 0) Δt μ 1 X = some st) : -- --- CONCL ---
    NonlinearSys.IsInnerMinkDiffCorrectedCert IMD.sys 0 Δt IMD.ops (fun _ => IMD.Z) X
      st := by -- --- PROOF ---
  unfold NonlinearSys.innerMinkDiffCorrectedStep at h
  obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
  -- a run of `ẋ = 0` on `[0, t]` is constant
  have hconst : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝ → Vec ℝ 1,
      (∀ s ∈ Icc 0 t, HasDerivWithinAt x (IMD.sys.f (x s) 0) (Icc 0 t) s) → x t = x 0 :=
    fun t ht x hd => constant_of_has_deriv_right_zero (fun s hs => (hd s hs).continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))) t ⟨ht, le_rfl⟩
  have hsum : ({0} + {0} : Set (Vec ℝ 1)) = {0} := by rw [singleton_add_singleton, add_zero]
  refine ⟨isCompact_singleton, convex_singleton _, singleton_nonempty _, fun e he => ?_,
    fun e he => ?_, ?_, ?_, singleton_nonempty _, fun e he => ?_, fun x hx => ?_, ?_,
    fun x₀ _ x hx0 hd => ?_, fun t ht x₀ _ x hx0 hd => ?_⟩
  · rw [mem_singleton_iff.mp he, neg_zero]; rfl
  · show (2 : ℝ) • (0 : Vec ℝ 1) - e ∈ ({0} : Set (Vec ℝ 1))
    rw [mem_singleton_iff.mp he, smul_zero, sub_zero]; rfl
  · exact hsum ▸ isCompact_singleton
  · exact hsum ▸ convex_singleton _
  · -- `E = {0}` and `c = 0`
    have he' : e = 0 := mem_singleton_iff.mp (hsum ▸ he)
    show (2 : ℝ) • ((0 : Vec ℝ 1) + 0) - e ∈ ({0} : Set (Vec ℝ 1)) + {0}
    rw [hsum, he', add_zero, smul_zero, sub_zero]; rfl
  · -- `[0, 1] = 1/2 + β/2`, `β = 2x - 1`
    refine ⟨fun _ => 2 * x 0 - 1, fun _ => abs_le.mpr ⟨by linarith [(hX hx).1],
      by linarith [(hX hx).2]⟩, funext fun i => ?_⟩
    fin_cases i
    simp [IMD.Z]
    ring
  · -- the constant run, `0`-Lipschitz field
    refine ⟨univ, 0, (LipschitzWith.const' (0 : Vec ℝ 1)).lipschitzOnWith, fun x₀ _ =>
      ⟨fun _ => x₀, rfl, fun t _ => ⟨mem_univ _, hasDerivWithinAt_const _ _ _⟩⟩⟩
  · -- (21): `x(Δt) = x₀`, `A = 0`, `R_con = 0`
    rw [hconst Δt hΔt.le x hd, hx0]
    simp [IMD.ops, IMD.sys]
  · -- the chord of `x₀` is `x₀`
    rw [hconst t ht.1 x hd, hx0]
    simp [IMD.ops, IMD.sys]

/-- Every step of the run, one step over `[0, 1]`, has its certificate. -/
theorem IMD.hcert : -- --- CONCL ---
    ∀ j < 1, ∀ (X Y : Set (Vec ℝ 1)) (st : NonlinearSys.InnerMinkDiffState 1 Unit),
    NonlinearSys.innerMinkDiffCorrectedLoop IMD.ops (fun _ => IMD.Z) (fun x => IMD.sys.f x 0)
      (1 / (1 : ℕ)) (11 / 10) 1 j IMD.X₀ ∅ = some (X, Y) →
    NonlinearSys.innerMinkDiffCorrectedStep IMD.ops (fun _ => IMD.Z) (fun x => IMD.sys.f x 0)
      (1 / (1 : ℕ)) (11 / 10) 1 X = some st →
    NonlinearSys.IsInnerMinkDiffCorrectedCert IMD.sys 0 (1 / (1 : ℕ)) IMD.ops (fun _ => IMD.Z) X
      st := by -- --- PROOF ---
  intro j hj X Y st hl hst
  obtain rfl : j = 0 := by omega
  simp only [NonlinearSys.innerMinkDiffCorrectedLoop, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, -⟩ := hl
  exact IMD.cert (by norm_num) _ subset_rfl st hst

-- the run returns a set holding `1/2`, and the theorem places it in `R([0, 1])`
example : ∃ Rτ ∈ NonlinearSys.innerMinkDiffCorrected IMD.ops (fun _ => IMD.Z)
      (fun x => IMD.sys.f x 0) IMD.X₀ 1 1 1,
    (fun _ => 1 / 2 : Vec ℝ 1) ∈ Rτ ∧
      Rτ ⊆ ⋃ t ∈ Icc 0 1, IMD.sys.reachSetExact (S := 𝒮) (Icc 0 t) IMD.X₀ {0} t := by
  -- the step's remainder loop stops at its first pass
  obtain ⟨st, hst⟩ : ∃ st, NonlinearSys.innerMinkDiffCorrectedStep IMD.ops (fun _ => IMD.Z)
      (fun x => IMD.sys.f x 0) (1 / (1 : ℕ)) (11 / 10) 1 IMD.X₀ = some st :=
    ⟨_, rfl⟩
  have hrun : NonlinearSys.innerMinkDiffCorrected IMD.ops (fun _ => IMD.Z)
      (fun x => IMD.sys.f x 0) IMD.X₀ 1 1 1 = some (∅ ∪ st.Rtauk) := by
    simp only [NonlinearSys.innerMinkDiffCorrected, NonlinearSys.innerMinkDiffCorrectedLoop, hst,
      Option.bind_some, Option.map_some]
  refine ⟨_, hrun, ?_, NonlinearSys.innerMinkDiffCorrected_subset_reachSetExact IMD.ops _ IMD.sys 0
    {0} rfl IMD.X₀ ?_ one_pos one_pos 1 IMD.hcert _ hrun⟩
  · -- `µ = 0`, so `1/2 ∈ X₀ ⊖ {0} ⊖ {0}` is in `R̂(τ₀)`
    unfold NonlinearSys.innerMinkDiffCorrectedStep at hst
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hst
    have hμ : (genOpNorm₂ fun j => (exp ((1 / ((1 : ℕ) : ℝ)) • (0 : Mat ℝ 1 1)) - 1) *ᵥ IMD.Z.G j)
        = 0 := by
      have h0 : (fun j => (exp ((1 / ((1 : ℕ) : ℝ)) • (0 : Mat ℝ 1 1)) - 1) *ᵥ IMD.Z.G j) =
          fun _ => 0 := funext fun _ => by simp
      rw [h0, IMD.aux_genOpNorm₂_zero]
    refine Or.inr ?_
    show (fun _ => (1 : ℝ) / 2) ∈ (fun x => x + (2 : ℝ) • ((0 : Vec ℝ 1) + 0)) '' minkowskiDiff
      (convexHull ℝ (minkowskiDiff (minkowskiDiff IMD.X₀ {0}) {0} ∪ _))
      {y : Vec ℝ 1 | ‖y‖₂ ≤ Real.sqrt ((1 : ℕ) : ℝ) *
        genOpNorm₂ fun j => (exp ((1 / ((1 : ℕ) : ℝ)) • (0 : Mat ℝ 1 1)) - 1) *ᵥ IMD.Z.G j}
    rw [hμ, mul_zero]
    refine ⟨fun _ => 1 / 2, fun y hy => subset_convexHull ℝ _ (Or.inl fun e he e' he' => ?_),
      by simp⟩
    -- `‖y‖₂ ≤ 0` makes `y = 0`, and `1/2 ∈ [0, 1]`
    have hy0 : y = 0 := funext fun i => abs_nonpos_iff.mp ((abs_le_norm₂ y i).trans hy)
    rw [hy0, mem_singleton_iff.mp he, mem_singleton_iff.mp he']
    norm_num [IMD.X₀]
  · -- `[0, 1]` is convex
    intro x hx z hz a b ha hb hab
    exact ⟨by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; nlinarith [hx.1, hz.1],
      by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; nlinarith [hx.2, hz.2]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
