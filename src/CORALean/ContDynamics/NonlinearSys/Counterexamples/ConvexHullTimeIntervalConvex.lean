module

public import CORALean.ContDynamics.NonlinearSys.Theorems.ExpSmulShear
public import CORALean.ContDynamics.NonlinearSys.Theorems.InnerAbstrErrShear
public import CORALean.ContDynamics.NonlinearSys.Theorems.InnerCurvatureErrorShear
public import CORALean.ContDynamics.NonlinearSys.Theorems.InnerLagrangeRemainderShear
public import CORALean.ContSet.ContSet.Interfaces
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# The time-interval inner set of L-CSS 2024 fails for a convex initial set too

[1, Prop. 2] claims `conv((X₀ ⊖ C) ⊖ R̂_err, R̂(Δt) ⊖ C) + 2c ⊆ R([0, Δt])` (23) for compact,
nonempty `X₀`; `convexHull_timeInterval_counterexample` refutes it for a nonconvex `X₀`, this file
for the box `[-1/10, 1/10] × [-1, 1]` under the shear `ẋ = (x₂, 0)`, `Δt = 1`, every term computed:
`cen(X₀)`, any `(0, y)`, `|y| ≤ 9/10`, fixed to `0`, so `x* = 0`, `w = 0` (6); `A² = 0`, so
`e^{A} = I + A`, `C = {0}` (17) at `η ≥ 1`, `L̂ = 0` (9) on any region, `R̂_err = {0}` (13), `c = 0`
for any centers (a Chebyshev center lies in its set): `⊖ {0}` and `+ 2c` change nothing. (23)
holds `(1/2, 0) = ½((0, -1) + e^{A}(0, 1))`, on no run: it starts on `x₂ = 0`, where `ẋ = 0`. At
`η = 0`, `C = [-1, 1] × {0}` empties both differences. [1]'s proof uses Lemma 1 off the chords.

## Inputs
* `η` – Taylor order

## Hypotheses
* `hη` – Taylor order positive

## Conclusion
* a point of (23)'s set for a convex box is reached by no run

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   21-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] fails for the shear `ẋ = (x₂, 0)` from the box `[-1/10, 1/10] × [-1, 1]`, `Δt = 1`,
`η ≥ 1`, `cen(X₀) = 0`: for (9) on any region and any centers of `C`, `R̂_err`, the set (23) holds
`(1/2, 0)`, on no run over `[0, 1]`; `e^{A} = I + A`, `X₀` convex, compact, nonempty. -/
theorem convexHull_timeInterval_convex_counterexample (η : ℕ) (hη : 1 ≤ η) : -- --- CONCL ---
    let f : Vec ℝ 2 → Vec ℝ 2 := fun x => ![x 1, 0]
    let X₀ : Set (Vec ℝ 2) := Icc ![-1 / 10, -1] ![1 / 10, 1]
    let Δt : ℝ := 1
    let A : Mat ℝ 2 2 := !![0, 1; 0, 0]
    let xstar : Vec ℝ 2 := 0 + (Δt / 2) • f 0 -- line 4, cen(X₀) = 0
    let w := f xstar -- (6)
    let C := NonlinearSys.innerCurvatureError η Δt A ((· - xstar) '' X₀) w -- (17), box(X₀) = X₀
    let Rcon := ∫ θ in (0 : ℝ)..Δt, exp ((Δt - θ) • A) *ᵥ w -- (12)
    let Raff := (· + Rcon) '' ((exp (Δt • A) *ᵥ ·) '' X₀) -- (10), (11)
    exp A = 1 + A ∧ Convex ℝ X₀ ∧ IsCompact X₀ ∧ X₀.Nonempty ∧
      (∀ x₀ ∈ X₀, ∀ x : ℝ → Vec ℝ 2, x 0 = x₀ →
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x (f (x t)) (Icc 0 1) t) → x 1 = exp A *ᵥ x₀) ∧
      (∀ Ω : Set (Vec ℝ 2),
        let Lhat := NonlinearSys.innerLagrangeRemainder f xstar Ω -- (9)
        let Rerr := NonlinearSys.innerAbstrErr η Δt A Lhat -- (13)
        C.Nonempty ∧ Rerr.Nonempty ∧ ∀ cC ∈ C, ∀ cE ∈ Rerr,
          let c := cC + cE -- line 14
          let RΔt := (· + (2 : ℝ) • cE) '' minkowskiDiff Raff Rerr -- (20)
          ![1 / 2, 0] ∈ (· + (2 : ℝ) • c) '' -- (23)
            convexHull ℝ (minkowskiDiff (minkowskiDiff X₀ C) Rerr ∪ minkowskiDiff RΔt C)) ∧
      ∀ x₀ ∈ X₀, ∀ x : ℝ → Vec ℝ 2, x 0 = x₀ →
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x (f (x t)) (Icc 0 1) t) →
        ∀ t ∈ Icc (0 : ℝ) 1, x t ≠ ![1 / 2, 0] := by -- --- PROOF ---
  intro f X₀ Δt A xstar w C Rcon Raff
  -- `e^{A} = I + A`, as `A² = 0`
  have hexp : exp A = 1 + A := by
    simpa using NonlinearSys.exp_smul_shear 1
  -- `e^{A} x = (x₁ + x₂, x₂)`
  have heA : ∀ y : Vec ℝ 2, exp A *ᵥ y = ![y 0 + y 1, y 1] := fun y => by
    rw [hexp, Matrix.add_mulVec, Matrix.one_mulVec]
    ext i; fin_cases i <;> simp [A, Matrix.vecHead, Matrix.vecTail]
  have hne : X₀.Nonempty := nonempty_Icc.mpr fun i => by fin_cases i <;> norm_num
  -- line 4 and (6): `x* = 0`, `w = f(0) = 0`
  have hx : xstar = 0 := by
    ext i; fin_cases i <;> simp [xstar, f]
  have hw : w = 0 := by
    ext i; fin_cases i <;> simp [w, hx, f]
  -- (17): `C = {0}`, as `F = {0}` and `w = 0`
  have hC : C = {0} := by
    show NonlinearSys.innerCurvatureError η 1 !![0, 1; 0, 0] ((· - xstar) '' X₀) w = {0}
    rw [hw]
    exact NonlinearSys.innerCurvatureError_shear 1 hη (hne.image _)
  -- (12) and (10): `R_con = 0`, so `R_aff(Δt) = e^{A} X₀`
  have hRcon : Rcon = 0 := by
    simp [Rcon, hw]
  have hRaff : Raff = (exp A *ᵥ ·) '' X₀ := by
    simp only [Raff, hRcon, add_zero, Set.image_id', Δt, one_smul]
  -- a difference by `{0}` changes nothing
  have hmd : ∀ T : Set (Vec ℝ 2), minkowskiDiff T {0} = T := fun T => by
    ext x; simp [minkowskiDiff]
  -- a function with zero derivative on `[0, 1]` is constant there
  have hconst : ∀ g : ℝ → ℝ, (∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g 0 (Icc 0 1) s) →
      ∀ t ∈ Icc (0 : ℝ) 1, g t = g 0 := fun g hd =>
    constant_of_has_deriv_right_zero (fun s hs => (hd s hs).continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
  -- every run is `x t = (x₀₁ + t x₀₂, x₀₂)` on `[0, 1]`
  have hrun : ∀ x : ℝ → Vec ℝ 2,
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x (f (x t)) (Icc 0 1) t) →
      ∀ t ∈ Icc (0 : ℝ) 1, x t 1 = x 0 1 ∧ x t 0 = x 0 0 + t * x 0 1 := by
    intro x hder
    have h1 : ∀ t ∈ Icc (0 : ℝ) 1, x t 1 = x 0 1 :=
      hconst (fun s => x s 1) fun s hs => by simpa [f] using hasDerivWithinAt_pi.mp (hder s hs) 1
    have h0 : ∀ t ∈ Icc (0 : ℝ) 1, x t 0 - t * x 0 1 = x 0 0 - 0 * x 0 1 :=
      hconst (fun s => x s 0 - s * x 0 1) fun s hs => by
        -- `x₁ - t x₀₂` has derivative `x₂ - x₀₂ = 0`
        have hx : HasDerivWithinAt (fun s => x s 0) (x s 1) (Icc 0 1) s := by
          simpa [f] using hasDerivWithinAt_pi.mp (hder s hs) 0
        have h2 : HasDerivWithinAt (fun s : ℝ => s * x 0 1) (1 * x 0 1) (Icc 0 1) s :=
          (hasDerivWithinAt_id s (Icc 0 1)).mul_const (x 0 1)
        have h3 : HasDerivWithinAt (fun s => x s 0 - s * x 0 1) (x s 1 - 1 * x 0 1)
            (Icc 0 1) s := hx.sub h2
        rwa [h1 s hs, one_mul, sub_self] at h3
    exact fun t ht => ⟨h1 t ht, by linarith [h0 t ht]⟩
  -- membership in the box, coordinatewise
  have hmem : ∀ y : Vec ℝ 2, y ∈ X₀ ↔ y 0 ∈ Icc (-1 / 10) (1 / 10) ∧ y 1 ∈ Icc (-1) 1 := by
    intro y
    simp only [X₀, mem_Icc, Pi.le_def, Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  -- `X₀` is a box, convex, compact and nonempty
  refine ⟨hexp, convex_Icc _ _, isCompact_Icc, hne, ?_, ?_, ?_⟩
  · -- the run ends at `e^{A} x₀`
    intro x₀ _ x hx0 hder
    obtain ⟨h1, h0⟩ := hrun x hder 1 ⟨zero_le_one, le_rfl⟩
    rw [heA]
    ext i; fin_cases i <;> simp [h1, h0, hx0]
  · intro Ω Lhat Rerr
    -- (9): `L̂ = {0}`, as `D²f ≡ 0`; (13): `R̂_err(0) = {0}`
    have hL : Lhat = {0} := NonlinearSys.innerLagrangeRemainder_shear xstar Ω
    have hE : Rerr = {0} := by
      show NonlinearSys.innerAbstrErr η 1 !![0, 1; 0, 0] Lhat = {0}
      rw [hL]
      exact NonlinearSys.innerAbstrErr_shear 1 hη
    refine ⟨hC ▸ singleton_nonempty 0, hE ▸ singleton_nonempty 0, fun cC hcC cE hcE => ?_⟩
    -- line 14: `c = 0`; the differences by `{0}` and the shift by `2c` drop out
    rw [hC, mem_singleton_iff] at hcC
    rw [hE, mem_singleton_iff] at hcE
    simp only [hC, hE, hcC, hcE, hmd, hRaff, add_zero, smul_zero, Set.image_id']
    -- the midpoint of `(0, -1) ∈ X₀` and `(1, 1) = e^{A}(0, 1)`
    have h0 : (![0, -1] : Vec ℝ 2) ∈ X₀ ∪ (exp A *ᵥ ·) '' X₀ :=
      Or.inl ((hmem _).mpr ⟨by simp; norm_num, by simp⟩)
    have h1 : (![1, 1] : Vec ℝ 2) ∈ X₀ ∪ (exp A *ᵥ ·) '' X₀ := by
      refine Or.inr ⟨![0, 1], (hmem _).mpr ⟨by simp; norm_num, by simp⟩, ?_⟩
      show exp A *ᵥ ![0, 1] = ![1, 1]
      rw [heA]
      ext i; fin_cases i <;> simp
    refine segment_subset_convexHull h0 h1
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; fin_cases i <;> simp
  · -- a run through `(1/2, 0)` starts on `x₂ = 0` and keeps its first coordinate
    intro x₀ hx₀ x hx0 hder t ht hxt
    obtain ⟨h1, h0⟩ := hrun x hder t ht
    have e1 := congrFun hxt 1
    have e0 := congrFun hxt 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    rw [hx0] at h1 h0
    have hb := ((hmem x₀).mp hx₀).1
    -- so `x₀₂ = 0` and `x₀₁ = 1/2`, outside `[-1/10, 1/10]`
    rw [e1] at h1
    rw [e0, ← h1, mul_zero, add_zero] at h0
    rw [← h0] at hb
    norm_num at hb

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
