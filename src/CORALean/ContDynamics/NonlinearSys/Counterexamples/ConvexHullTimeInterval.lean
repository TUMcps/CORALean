module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerAbstrErr
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerCurvatureError
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerLagrangeRemainder
public import CORALean.ContSet.ContSet.Interfaces
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# The time-interval inner set of L-CSS 2024 is not inside the reachable set

[1, Prop. 2] claims `conv((X₀ ⊖ C) ⊖ R̂_err, R̂(Δt) ⊖ C) + 2c ⊆ R([0, Δt])` (23) for compact,
nonempty `X₀`. For `ẋ = w = (0, 1)` the linearization is exact (`A = 0`, `x*` of line 4 any point,
as `cen(X₀)` of the two squares `([0, 1/10] ∪ [9/10, 1]) × [0, 1/10]` has no formula): `e^{A} = I`,
`C = {0}` (17) at every `η`, `η = 0` included (`E = 0`), though `w ≠ 0`, `R_con = Δt w` (12),
`L̂ = 0` (9) on any region, `R̂_err = {0}` (13), `c = 0` for any centers (a Chebyshev center lies
in its set), so `⊖ {0}` and `+ 2c` change nothing and `R̂(Δt) = X₀ + Δt w`. (23) holds `(1/2, 1/2)`
= `½((0, 0) + (1, 1))`, on no run, as `x₁` stays in `X₀`'s columns. [1]'s proof uses Lemma 1 off
the chords: points of the hull need not be `x₀ + (t/Δt)(R_aff - x₀)` for one `x₀`.

## Inputs
* `η` – Taylor order
* `xcen` – a center of `X₀`

## Hypotheses
* none

## Conclusion
* a point of (23)'s set for a nonconvex initial set is reached by no run

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
* [2] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   21-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Pointwise Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [2, (20)]: `E(Δt, η) = e^{|A|Δt} - Σ_{i≤η} (|A|Δt)ⁱ/i! = 0` for `A = 0`, any `η`. -/
private theorem NonlinearSys.aux_expRemainderMat_zero {n : ℕ} (Δt : ℝ) (η : ℕ) : -- --- CONCL ---
    Real.MatExp.expRemainderMat (0 : Mat ℝ n n) Δt η = 0 := by -- --- PROOF ---
  have habs : Real.MatExp.absMat (0 : Mat ℝ n n) = 0 := by
    ext i j; simp [Real.MatExp.absMat]
  have htay : Real.MatExp.expTaylor (0 : Mat ℝ n n) η = 1 := by
    rw [Real.MatExp.expTaylor, Finset.sum_eq_single 0]
    · simp
    · intro i _ hi
      rw [zero_pow hi, smul_zero]
    · simp
  rw [Real.MatExp.expRemainderMat, habs, smul_zero, NormedSpace.exp_zero, htay, sub_self]

/-- (9): `L = [0, 0]` for a constant `f`, as `D²f ≡ 0`. -/
private theorem NonlinearSys.aux_innerLagrangeRemainder_const {n : ℕ} (w xstar : Vec ℝ n)
    (X : Set (Vec ℝ n)) : -- --- CONCL ---
    NonlinearSys.innerLagrangeRemainder (fun _ : Vec ℝ n => w) xstar X = {0} := by -- --- PROOF ---
  have hD : fderiv ℝ (fderiv ℝ (fun _ : Vec ℝ n => w)) = 0 := by
    rw [show fderiv ℝ (fun _ : Vec ℝ n => w) = fun _ => 0 from
      funext fun _ => fderiv_const_apply w]
    funext y; exact fderiv_const_apply 0
  simp only [NonlinearSys.innerLagrangeRemainder, hD, Pi.zero_apply, _root_.zero_apply,
    abs_zero, Real.iSup_const_zero]
  have hl : (fun i : Fin n => (fun j => ⨆ y ∈ X, |y j - xstar j|) ⬝ᵥ
      ((fun _ _ => (0 : ℝ)) *ᵥ fun j => ⨆ y ∈ X, |y j - xstar j|) / 2) = 0 := by
    ext i; simp [Matrix.mulVec, dotProduct]
  rw [hl, neg_zero, Set.Icc_self]

/-- (13): `R̂_err(0) = {0}` for `A = 0` and any `η`. -/
private theorem NonlinearSys.aux_innerAbstrErr_zero {n : ℕ} (Δt : ℝ) (η : ℕ) : -- --- CONCL ---
    NonlinearSys.innerAbstrErr η Δt (0 : Mat ℝ n n) {0} = {0} := by -- --- PROOF ---
  have h0 : (0 : Mat ℝ n n) ∈ Real.MatExp.expRemainderInterval (0 : Mat ℝ n n) Δt η :=
    fun j k => by simp [NonlinearSys.aux_expRemainderMat_zero Δt η]
  have h1 : ∀ M : Mat ℝ n n, (fun l => M *ᵥ l) '' ({0} : Set (Vec ℝ n)) = 0 := fun M => by
    rw [Set.image_singleton, Matrix.mulVec_zero, Set.singleton_zero]
  simp only [NonlinearSys.innerAbstrErr, h1, Finset.sum_const_zero, zero_add]
  rw [← Set.singleton_zero]
  exact Set.biUnion_const ⟨0, h0⟩ _

/-- [2, (19), (28)]: `F = G = {0}` for `A = 0`, any `η`. -/
private theorem NonlinearSys.aux_zero_depCurvature {n : ℕ} (Δt : ℝ) (η : ℕ) : -- --- CONCL ---
    (STL.depCurvatureF (0 : Mat ℝ n n) Δt η).construct = {0} ∧
      (STL.depCurvatureG (0 : Mat ℝ n n) Δt η).construct = {0} := by -- --- PROOF ---
  have hE := NonlinearSys.aux_expRemainderMat_zero (n := n) Δt η
  have hT : ∀ i j k, Real.MatExp.corrTerm (0 : Mat ℝ n n) Δt (i + 2) j k = 0 := fun i j k => by
    simp [Real.MatExp.corrTerm, zero_pow (Nat.succ_ne_zero (i + 1))]
  have hK : ∀ i j k, Real.MatExp.constCorrTerm (0 : Mat ℝ n n) Δt i j k = 0 := fun i j k => by
    simp [Real.MatExp.constCorrTerm, zero_pow (Nat.succ_ne_zero i)]
  constructor <;> (
    ext M
    simp only [Real.Interval.construct, STL.depCurvatureF, STL.depCurvatureG, hT, hK, hE,
      min_self, max_self, Finset.sum_const_zero, Matrix.zero_apply, sub_zero, add_zero, mul_zero,
      mem_setOf_eq, mem_singleton_iff, Entrywise.entry_mat]
    constructor
    · intro h; ext j k; exact le_antisymm (h (j, k)).2 (h (j, k)).1
    · rintro rfl p; simp)

/-- (17): `C = F box(X₀) ⊕ G w = {0}` for `A = 0`, any `η`, any `w` and a nonempty box. -/
private theorem NonlinearSys.aux_innerCurvatureError_zero {n : ℕ} (Δt : ℝ) (η : ℕ)
    {B : Set (Vec ℝ n)} (hB : B.Nonempty) (w : Vec ℝ n) :
    NonlinearSys.innerCurvatureError η Δt (0 : Mat ℝ n n) B w = {0} := by
  obtain ⟨hF, hG⟩ := NonlinearSys.aux_zero_depCurvature (n := n) Δt η
  simp only [NonlinearSys.innerCurvatureError, hF, hG, Set.biUnion_singleton,
    Matrix.zero_mulVec, hB.image_const, Set.singleton_add_singleton, add_zero]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] fails for `ẋ = (0, 1)` from two squares, `Δt = 1`, any `η` and any `cen(X₀)`: for
(9) on any region and any centers of `C`, `R̂_err`, the set (23) holds `(1/2, 1/2)`, on no run over
`[0, 1]`; `A = 0`, so `x(Δt) = x₀ + R_con`, `X₀` compact, nonempty. -/
theorem convexHull_timeInterval_counterexample (η : ℕ) (xcen : Vec ℝ 2) : -- --- CONCL ---
    let f : Vec ℝ 2 → Vec ℝ 2 := fun _ => ![0, 1]
    let X₀ : Set (Vec ℝ 2) := {x | (x 0 ∈ Icc 0 (1 / 10) ∨ x 0 ∈ Icc (9 / 10) 1) ∧
      x 1 ∈ Icc 0 (1 / 10)}
    let Δt : ℝ := 1
    let A : Mat ℝ 2 2 := 0 -- `Df = 0`
    let xstar : Vec ℝ 2 := xcen + (Δt / 2) • f xcen -- line 4
    let w := f xstar - A *ᵥ xstar -- (6)
    let C := NonlinearSys.innerCurvatureError η Δt A
      ((· - xstar) '' Icc ![0, 0] ![1, 1 / 10]) w -- (17), box(X₀)
    let Rcon := ∫ θ in (0 : ℝ)..Δt, exp ((Δt - θ) • A) *ᵥ w -- (12)
    let Raff := (· + Rcon) '' ((exp (Δt • A) *ᵥ ·) '' X₀) -- (10), (11)
    IsCompact X₀ ∧ X₀.Nonempty ∧
      (∀ x₀ ∈ X₀, ∀ x : ℝ → Vec ℝ 2, x 0 = x₀ →
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x (f (x t)) (Icc 0 1) t) →
        x 1 = exp (Δt • A) *ᵥ x₀ + Rcon) ∧
      (∀ Ω : Set (Vec ℝ 2),
        let Lhat := NonlinearSys.innerLagrangeRemainder f xstar Ω -- (9)
        let Rerr := NonlinearSys.innerAbstrErr η Δt A Lhat -- (13)
        C.Nonempty ∧ Rerr.Nonempty ∧ ∀ cC ∈ C, ∀ cE ∈ Rerr,
          let c := cC + cE -- line 14
          let RΔt := (· + (2 : ℝ) • cE) '' minkowskiDiff Raff Rerr -- (20)
          ![1 / 2, 1 / 2] ∈ (· + (2 : ℝ) • c) '' -- (23)
            convexHull ℝ (minkowskiDiff (minkowskiDiff X₀ C) Rerr ∪ minkowskiDiff RΔt C)) ∧
      ∀ x₀ ∈ X₀, ∀ x : ℝ → Vec ℝ 2, x 0 = x₀ →
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x (f (x t)) (Icc 0 1) t) →
        ∀ t ∈ Icc (0 : ℝ) 1, x t ≠ ![1 / 2, 1 / 2] := by -- --- PROOF ---
  intro f X₀ Δt A xstar w C Rcon Raff
  -- `e^{AΔt} = I`, as `A = 0`
  have hexp : exp (Δt • A) = 1 := by simp [A]
  -- (6): `w = f(x*) - A x* = (0, 1)`
  have hw : w = ![0, 1] := by simp [w, A, f]
  -- (12): `R_con = Δt w = (0, 1)`
  have hRcon : Rcon = ![0, 1] := by
    simp [Rcon, hw, A, Δt]
  -- (10), (11): `R_aff = X₀ + Δt w`
  have hRaff : Raff = (· + ![0, 1]) '' X₀ := by
    simp only [Raff, hRcon, hexp, Matrix.one_mulVec, Set.image_id']
  have hne : X₀.Nonempty := ⟨![0, 0], Or.inl ⟨le_refl _, by norm_num⟩, by simp⟩
  -- (17): `C = {0}`, as `F = G = {0}`, though `w ≠ 0`
  have hC : C = {0} := by
    refine NonlinearSys.aux_innerCurvatureError_zero Δt η ?_ w
    exact (nonempty_Icc.mpr fun i => by fin_cases i <;> norm_num).image _
  -- a difference by `{0}` changes nothing
  have hmd : ∀ T : Set (Vec ℝ 2), minkowskiDiff T {0} = T := fun T => by
    ext x; simp [minkowskiDiff]
  -- a function with zero derivative on `[0, 1]` is constant there
  have hconst : ∀ g : ℝ → ℝ, (∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g 0 (Icc 0 1) s) →
      ∀ t ∈ Icc (0 : ℝ) 1, g t = g 0 := fun g hd =>
    constant_of_has_deriv_right_zero (fun s hs => (hd s hs).continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
  -- every run is `x t = x₀ + t (0, 1)` on `[0, 1]`
  have hrun : ∀ x : ℝ → Vec ℝ 2,
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x (f (x t)) (Icc 0 1) t) →
      ∀ t ∈ Icc (0 : ℝ) 1, x t 0 = x 0 0 ∧ x t 1 = x 0 1 + t := by
    intro x hder
    have h0 : ∀ t ∈ Icc (0 : ℝ) 1, x t 0 = x 0 0 :=
      hconst (fun s => x s 0) fun s hs => by simpa [f] using hasDerivWithinAt_pi.mp (hder s hs) 0
    have h1 : ∀ t ∈ Icc (0 : ℝ) 1, x t 1 - t = x 0 1 - 0 :=
      hconst (fun s => x s 1 - s) fun s hs => by
        -- `x₂ - t` has derivative `1 - 1 = 0`
        have hx : HasDerivWithinAt (fun s => x s 1) 1 (Icc 0 1) s := by
          simpa [f] using hasDerivWithinAt_pi.mp (hder s hs) 1
        have h3 : HasDerivWithinAt (fun s => x s 1 - s) (1 - 1) (Icc 0 1) s :=
          hx.sub (hasDerivWithinAt_id s (Icc 0 1))
        rwa [sub_self] at h3
    exact fun t ht => ⟨h0 t ht, by linarith [h1 t ht]⟩
  refine ⟨?_, hne, ?_, ?_, ?_⟩
  · -- two compact squares
    have : X₀ = Icc ![0, 0] ![1 / 10, 1 / 10] ∪ Icc ![9 / 10, 0] ![1, 1 / 10] := by
      ext y
      simp only [X₀, mem_setOf_eq, mem_union, mem_Icc, Pi.le_def, Fin.forall_fin_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      tauto
    rw [this]
    exact isCompact_Icc.union isCompact_Icc
  · -- the run ends at `e^{AΔt} x₀ + R_con = x₀ + w`
    intro x₀ _ x hx0 hder
    obtain ⟨h0, h1⟩ := hrun x hder 1 ⟨zero_le_one, le_rfl⟩
    rw [hexp, hRcon, Matrix.one_mulVec]
    ext i; fin_cases i <;> simp [h0, h1, hx0]
  · intro Ω Lhat Rerr
    -- (9): `L̂ = {0}`, as `D²f ≡ 0`; (13): `R̂_err(0) = {0}`
    have hL : Lhat = {0} := NonlinearSys.aux_innerLagrangeRemainder_const _ xstar Ω
    have hE : Rerr = {0} := by
      show NonlinearSys.innerAbstrErr η Δt A Lhat = {0}
      rw [hL]
      exact NonlinearSys.aux_innerAbstrErr_zero Δt η
    refine ⟨hC ▸ singleton_nonempty 0, hE ▸ singleton_nonempty 0, fun cC hcC cE hcE => ?_⟩
    -- line 14: `c = 0`; the differences by `{0}` and the shift by `2c` drop out
    rw [hC, mem_singleton_iff] at hcC
    rw [hE, mem_singleton_iff] at hcE
    simp only [hC, hE, hcC, hcE, hmd, hRaff, add_zero, smul_zero, Set.image_id']
    -- the midpoint of `(0, 0) ∈ X₀` and `(1, 1) = (1, 0) + w`
    have h0 : (![0, 0] : Vec ℝ 2) ∈ X₀ ∪ (· + ![0, 1]) '' X₀ :=
      Or.inl ⟨Or.inl ⟨le_refl _, by norm_num⟩, by simp⟩
    have h1 : (![1, 1] : Vec ℝ 2) ∈ X₀ ∪ (· + ![0, 1]) '' X₀ := by
      refine Or.inr ⟨![1, 0], ⟨Or.inr ⟨by simp; norm_num, by simp⟩, by simp⟩, ?_⟩
      ext i; fin_cases i <;> simp
    refine segment_subset_convexHull h0 h1
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; fin_cases i <;> simp
  · -- the first coordinate is constant along the run, so it stays in `X₀`'s columns
    intro x₀ hx₀ x hx0 hder t ht hxt
    obtain ⟨h0, _⟩ := hrun x hder t ht
    have h := congrFun hxt 0
    simp only [h0, hx0, Matrix.cons_val_zero] at h
    rcases hx₀.1 with h' | h' <;> rw [h] at h' <;> norm_num at h'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
