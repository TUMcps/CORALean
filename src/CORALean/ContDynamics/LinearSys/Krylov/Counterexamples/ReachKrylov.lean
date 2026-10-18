module

public import CORALean.ContDynamics.LinearSys.Definitions.IsCanonicalClassicalTrajectory
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Augment
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# CORA's `reach` with `linAlg = 'krylov'` misses a trajectory

`reach` (l. 80-81) runs `priv_reach_krylov` on `A = [0 0; 1 1]`, `B = [1; 0]`, `R0 = {0}`,
`U = zonotope(1)`, `tFinal = timeStep = t = 3`, `krylovError = t²/2`, `krylovStep = 1`,
`zonotopeOrder = 10`, `'girard'`. `U` becomes `uTrans = 1`, so `B uTrans = e₁` and every
input set is a point. `priv_krylov_R_uTrans` calls `priv_subspace_Krylov_individual_Jawecki`
on `[A e₁; 0 0]` from `e₃` at order `2` (l. 149-166), where Arnoldi does not break down and
Err_a `= t²/2` passes (`Krylov.jawecki_bound_cora_counterexample`). `R0` and `U` have no
generators, so no other Krylov subspace is built. The first time-point set (`aux_propagation`
l. 121-156) is `reduce(Htp + RTrans + zonotope(U_0_sol))`: `Htp = zonotope([0, εI])`,
`RTrans = zonotope([V E e₁, εI])`, `U_0_sol = 0`, `ε = krylovError`; no reduction at order `10`.
`V = [e₃ e₁]` has second row `0`, so the set lies in `|x₂| ≤ 2ε = 9`, while the run from `0`
under `u ≡ 1` has `x₂(3) = e³ - 4 > 16`. `E` is `expm(H t)`, quantified over every matrix;
the margin `7` exceeds any floating error, the Arnoldi steps on `0/1` data are exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's Krylov `reach`, step `1`, as printed for the example above: the Jawecki test accepts
order `2`, yet for every `expm` output `E` the time-point set misses `x(3)` of a run. -/
theorem Krylov.reach_krylov_counterexample : -- --- STMT ---
    let A : Mat ℝ 2 2 := !![0, 0; 1, 1]
    let u : Vec ℝ 2 := ![1, 0]
    let t : ℝ := 3
    let ε : ℝ := t ^ 2 / 2
    let C := Krylov.augment A u
    let v : Fin 3 → ℝ := Pi.single (Fin.last 2) 1
    let K := Krylov.arnoldi C v 2
    let τ : ℝ := K.2 2 1
    let γ : ℝ := K.2 1 0
    let V : Mat ℝ 2 2 := Matrix.of fun i j => K.1 j (Fin.castSucc i)
    let box : Vec ℝ 2 → Zonotope (Vec ℝ 2) := fun c => ⟨2, c, fun j => ε • Pi.single j 1⟩
    let Htp := box 0
    let RTrans : Mat ℝ 2 2 → Zonotope (Vec ℝ 2) := fun E => box (V *ᵥ (E *ᵥ Pi.single 0 1))
    let Rtp : Mat ℝ 2 2 → Zonotope (Vec ℝ 2) := fun E =>
      ((Htp.plus (RTrans E)).plus (Zonotope.ofPoint 0)).reduceGirard 10
    (K.2 1 0 = 1 ∧ τ = 1 ∧ ¬ ‖v‖₂ * (τ * γ * t ^ 2 / (Nat.factorial 2 : ℝ)) > ε) ∧
      ∃ x w : ℝ → Vec ℝ 2,
        (LinearSys.canonical A : LinearSys ℝ 2).IsCanonicalClassicalTrajectory (S := 𝒮)
          (Set.Icc 0 t) {0} {u} x w ∧
        ∀ E : Mat ℝ 2 2, x t ∉ (Rtp E).construct := by -- --- PROOF ---
  intro A u t ε C v K τ γ V box Htp RTrans Rtp
  have hC : C = !![0, 0, 1; 1, 1, 0; 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hv : v = ![0, 0, 1] := by
    ext i
    fin_cases i <;> rfl
  have hnv : ‖v‖₂ = 1 := by
    rw [hv]
    simp [norm₂, Fin.sum_univ_three]
  -- Arnoldi: `v⁽¹⁾ = e₃`, `v⁽²⁾ = e₁`, `h₂,₁ = h₃,₂ = 1`
  have hK0 : K.1 0 = ![0, 0, 1] := by
    show ‖v‖₂⁻¹ • v = _
    rw [hnv, hv, inv_one, one_smul]
  have hK1 : K.1 1 = ![1, 0, 0] := by
    ext i
    fin_cases i <;>
      simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, hC, hv, norm₂, Fin.sum_univ_three,
        dotProduct, vecHead, vecTail]
  have h10 : K.2 1 0 = 1 := by
    simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, hC, hv, norm₂, Fin.sum_univ_three,
      dotProduct, vecHead, vecTail]
  have h21 : K.2 2 1 = 1 := by
    simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, hC, hv, norm₂, Fin.sum_univ_three,
      dotProduct, vecHead, vecTail]
  refine ⟨⟨h10, h21, ?_⟩, ?_⟩
  · -- the loop exits at order `2`: `1 · 1 · 1 · 9/2 = ε`
    simp only [hnv, τ, γ, h21, h10, ε, t, Nat.factorial]
    norm_num
  -- the run from `0` under `u ≡ e₁`: `x(s) = (s, eˢ - 1 - s)`
  refine ⟨fun s => ![s, Real.exp s - 1 - s], fun _ => u, ⟨?_, ?_, ?_⟩, ?_⟩
  · show ![(0 : ℝ), Real.exp 0 - 1 - 0] ∈ ({0} : Set (Vec ℝ 2))
    rw [Set.mem_singleton_iff]
    ext i
    fin_cases i <;> simp
  · intro s _
    exact Set.mem_singleton u
  · intro s _
    refine HasDerivAt.hasDerivWithinAt ?_
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · refine (hasDerivAt_id s).congr_deriv ?_
      simp [A, u]
    · refine (((Real.hasDerivAt_exp s).sub_const 1).sub (hasDerivAt_id s)).congr_deriv ?_
      simp [A, u]
  -- every point of a box `⟨c, εI⟩` has `|z₂ - c₂| ≤ ε`
  have hbox : ∀ (c z : Vec ℝ 2), z ∈ (box c).construct → |z 1 - c 1| ≤ ε := by
    intro c z hz
    obtain ⟨β, hβ, hz⟩ := Zonotope.mem_construct_iff.1 hz
    have h := hz 1
    simp only [box, Fin.sum_univ_two] at h
    have hε : (0 : ℝ) ≤ ε := by positivity
    rw [h]
    simp only [Pi.smul_apply, smul_eq_mul]
    simp [abs_mul, abs_of_nonneg hε]
    exact mul_le_of_le_one_right hε (hβ 1)
  intro E hx
  -- `reduce` at order `10` keeps the `4` generators
  have hred : ∀ Z : Zonotope (Vec ℝ 2), Z.h = 4 → Z.reduceGirard 10 = Z := by
    intro Z hZ
    unfold Zonotope.reduceGirard
    rw [dif_neg (by omega)]
  have hh : ((Htp.plus (RTrans E)).plus (Zonotope.ofPoint 0)).h = 4 := rfl
  have hx' := hx
  simp only [Rtp] at hx'
  rw [hred _ hh, ← Zonotope.plus_exact, ← Zonotope.plus_exact] at hx'
  obtain ⟨y, ⟨a, ha, b, hb, rfl⟩, p, hp, hxe⟩ := hx'
  rw [Zonotope.mem_ofPoint_iff] at hp
  subst hp
  have ha1 := hbox 0 a ha
  have hb1 := hbox _ b hb
  -- `V` has second row `0`, so the Krylov center has `x₂ = 0`
  have hc1 : (V *ᵥ (E *ᵥ Pi.single 0 1)) 1 = 0 := by
    simp [V, mulVec, dotProduct, Fin.sum_univ_two, hK0, hK1]
  rw [hc1, sub_zero] at hb1
  simp only [Pi.zero_apply, sub_zero] at ha1
  have h2 := congrFun hxe 1
  simp only [Pi.add_apply, Pi.zero_apply, add_zero] at h2
  -- `x₂(3) = e³ - 4 > 2ε = 9`
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hlt : 9 < Real.exp 3 - 1 - 3 := by
    have h := pow_le_pow_left₀ (by norm_num) he.le 3
    rw [he3]
    norm_num at h ⊢
    linarith
  have hsum : |a 1 + b 1| ≤ 9 := by
    calc |a 1 + b 1| ≤ |a 1| + |b 1| := abs_add_le _ _
      _ ≤ ε + ε := add_le_add ha1 hb1
      _ = 9 := by norm_num [ε, t]
  have hx2 : (![t, Real.exp t - 1 - t] : Vec ℝ 2) 1 = Real.exp 3 - 1 - 3 := by
    simp [t]
  rw [h2, hx2] at hsum
  linarith [le_abs_self (Real.exp 3 - 1 - 3)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
