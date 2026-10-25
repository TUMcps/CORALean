module

public import CORALean.ContDynamics.LinearSys.Definitions.ClosedForm
public import CORALean.ContDynamics.LinearSys.Definitions.HeldInput
public import CORALean.ContDynamics.LinearSys.Definitions.HeldSim
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.ContDynamics.LinearSys.Theorems.HeldInputMeasurable

@[expose] public section

/-!
# The held-input run, sampled, is the discrete-time system

[1, Sec. 4.2]: under piecewise-constant inputs the continuous-time system is
"exactly computed via simulation" of [1]'s Eq. (18). `closedForm` under
`heldInput Δt v`, read at `t_k = k Δt`, is `heldSim`'s `x(k)`: each step splits
the integral at `t_k`, the part before is `e^{AΔt}` applied to the old state's,
and the part after sees only `v k`, which substituting `σ = t_{k+1} - s` turns
into `T v k`. The inputs only have to lie in some bounded set, which is what
makes each piece integrable.

## Inputs
* `sys` – linear system
* `U` – input set
* `Δt` – step length
* `x₀` – initial point
* `v` – held input values
* `k` – step index

## Hypotheses
* `hU` – input set bounded
* `hΔt` – step length positive
* `hv` – held values lie in the input set

## Conclusion
* the held-input run sampled at the step index is the discrete-time state

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- On the step `(k Δt, (k + 1) Δt]` the held input is `v k`. -/
theorem aux_heldInput_eq {Δt : ℝ} (hΔt : 0 < Δt) (v : ℕ → Vec ℝ n) (k : ℕ) {s : ℝ}
    (hs : s ∈ Set.Ioc ((k : ℝ) * Δt) ((k : ℝ) * Δt + Δt)) : -- --- CONCL ---
    LinearSys.heldInput Δt v s = v k := by -- --- PROOF ---
  have h1 : (k : ℝ) < s / Δt := by rw [lt_div_iff₀ hΔt]; exact hs.1
  have h2 : s / Δt ≤ ((k + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hΔt]; push_cast; linarith [hs.2]
  have hc : ⌈s / Δt⌉₊ = k + 1 :=
    (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).mpr ⟨by simpa using h1, h2⟩
  simp only [LinearSys.heldInput, hc, Nat.add_sub_cancel]

/-- One step of `closedForm`: the state at `a + Δt` is `e^{AΔt}` applied to the state at `a`,
plus `T w` from an input held at `w` over `(a, a + Δt]`. -/
theorem aux_closedForm_add (sys : LinearSys 𝕋 n) {U : S n}
    (hU : Bornology.IsBounded (construct U)) {a Δt : ℝ} (ha : 0 ≤ a) (hΔt : 0 ≤ Δt)
    (x₀ : Vec ℝ n) {u : ℝ → Vec ℝ n} (hu : ∀ s ∈ Set.Icc (0:ℝ) (a + Δt), u s ∈ construct U)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 (a + Δt)))) {w : Vec ℝ n}
    (hw : ∀ s ∈ Set.Ioc a (a + Δt), u s = w) : -- --- CONCL ---
    sys.closedForm x₀ u (a + Δt)
      = exp (Δt • toRealMat sys.A) *ᵥ sys.closedForm x₀ u a
        + MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ w := by -- --- PROOF ---
  set A := toRealMat sys.A
  have hmul : ∀ c d : ℝ, exp (c • A) * exp (d • A) = exp ((c + d) • A) := by
    intro c d
    have hc : Commute (c • A) (d • A) := ((Commute.refl A).smul_left c).smul_right d
    rw [add_smul]; exact (exp_add_of_commute hc).symm
  have hb : 0 ≤ a + Δt := add_nonneg ha hΔt
  have hab : a ≤ a + Δt := le_add_of_nonneg_right hΔt
  have hint : IntervalIntegrable (fun s => exp ((a + Δt - s) • A) *ᵥ u s) volume 0 (a + Δt) :=
    intervalIntegrable_expSub_mulVec hb hU hu hmeas
  have hint1 : IntervalIntegrable (fun s => exp ((a + Δt - s) • A) *ᵥ u s) volume 0 a :=
    hint.mono_set (by
      rw [Set.uIcc_of_le ha, Set.uIcc_of_le hb]; exact Set.Icc_subset_Icc_right hab)
  have hint2 : IntervalIntegrable (fun s => exp ((a + Δt - s) • A) *ᵥ u s) volume a (a + Δt) :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le hb]; exact Set.Icc_subset_Icc_left ha)
  have hinta : IntervalIntegrable (fun s => exp ((a - s) • A) *ᵥ u s) volume 0 a :=
    intervalIntegrable_expSub_mulVec ha hU (fun s hs => hu s ⟨hs.1, le_trans hs.2 hab⟩)
      (hmeas.mono_measure (Measure.restrict_mono (Set.Icc_subset_Icc_right hab) le_rfl))
  -- the part before `a`: `e^{AΔt}` comes out of the integral
  have h1 : ∫ s in (0:ℝ)..a, exp ((a + Δt - s) • A) *ᵥ u s
      = exp (Δt • A) *ᵥ ∫ s in (0:ℝ)..a, exp ((a - s) • A) *ᵥ u s := by
    have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm (mulVecL (exp (Δt • A))) hinta
    refine (integral_congr fun s _ => ?_).trans hcomm
    show exp ((a + Δt - s) • A) *ᵥ u s = exp (Δt • A) *ᵥ (exp ((a - s) • A) *ᵥ u s)
    rw [mulVec_mulVec, hmul]
    congr 3
    ring
  -- the part after `a`: only the held value, and `σ = a + Δt - s` makes it `T w`
  have h2 : ∫ s in a..(a + Δt), exp ((a + Δt - s) • A) *ᵥ u s
      = MatExp.expIntegral A Δt *ᵥ w := by
    have hcongr : ∫ s in a..(a + Δt), exp ((a + Δt - s) • A) *ᵥ u s
        = ∫ s in a..(a + Δt), exp ((a + Δt - s) • A) *ᵥ w :=
      integral_congr_ae (Filter.Eventually.of_forall fun s hs => by
        rw [Set.uIoc_of_le hab] at hs
        rw [hw s hs])
    rw [hcongr, intervalIntegral.integral_comp_sub_left (fun σ => exp (σ • A) *ᵥ w) (a + Δt),
      sub_self, add_sub_cancel_left]
    exact (Real.MatExp.expIntegral_mulVec A w hΔt).symm
  show exp ((a + Δt) • A) *ᵥ x₀ + ∫ s in (0:ℝ)..(a + Δt), exp ((a + Δt - s) • A) *ᵥ u s
    = exp (Δt • A) *ᵥ (exp (a • A) *ᵥ x₀ + ∫ s in (0:ℝ)..a, exp ((a - s) • A) *ᵥ u s)
      + MatExp.expIntegral A Δt *ᵥ w
  rw [← integral_add_adjacent_intervals hint1 hint2, h1, h2, mulVec_add, mulVec_mulVec, hmul,
    add_comm Δt a, add_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: the run under `heldInput Δt v`, read at `t_k = k Δt`, is [1]'s Eq. (18)'s
`x(k)`. -/
theorem LinearSys.closedForm_heldInput (sys : LinearSys 𝕋 n) {U : S n}
    (hU : Bornology.IsBounded (construct U)) {Δt : ℝ} (hΔt : 0 < Δt) (x₀ : Vec ℝ n)
    {v : ℕ → Vec ℝ n} (hv : ∀ j, v j ∈ construct U) (k : ℕ) : -- --- CONCL ---
    sys.closedForm x₀ (LinearSys.heldInput Δt v) (k * Δt)
      = sys.heldSim Δt x₀ v k := by -- --- PROOF ---
  induction k with
  | zero =>
    show _ = x₀
    simpa using sys.closedForm_zero x₀ (LinearSys.heldInput Δt v)
  | succ k ih =>
    have hk : (0:ℝ) ≤ k * Δt := mul_nonneg k.cast_nonneg hΔt.le
    have hstep := aux_closedForm_add sys hU hk hΔt.le x₀ (u := LinearSys.heldInput Δt v)
      (fun s _ => hv _)
      (LinearSys.heldInput_measurable Δt v).aestronglyMeasurable
      (fun s hs => aux_heldInput_eq hΔt v k hs)
    rw [show ((k + 1 : ℕ) : ℝ) * Δt = k * Δt + Δt by push_cast; ring, hstep, ih]
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
