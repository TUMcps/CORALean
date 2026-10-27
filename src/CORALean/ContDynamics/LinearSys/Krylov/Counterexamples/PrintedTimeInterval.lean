module

public import CORALean.ContDynamics.LinearSys.Krylov.Definitions.CorrectionSet
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
public import CORALean.Global.EuclideanNorm
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# The printed time-interval enclosure fails

[1, Thm. III.2] as printed, `R_h([0, δ]) ⊆ conv(X₀, R_h(δ)) ⊕ N` with
`N = ‖c‖V(c)F(c)e₁ ⊕ ⨁ᵢ ‖g⁽ⁱ⁾‖V(g⁽ⁱ⁾)F(g⁽ⁱ⁾)e₁`, fails for the shift `A e₁ = e₂`, `A e₂ = e₃`,
`A e₃ = 0`, `X₀ = (e₃, e₁)`, `δ = 1`, `η = 2`. Alg. 1 is exact there (`ε_norm = 0`), so
`R_h(1) = e^{A}X₀`, `F(e₁) e₁ = λ₂ e₃/2` with `λ₂ ∈ [-1/4, 0]`, `F(e₃) = 0`. `X₀` and `R_h(1)`
lie on the plane `x₃ - x₂/2 = 1` and `N` on its side `≤ 0`, while
`e^{A/2}(e₃ - e₁) = (-1, -1/2, 7/8)` has `x₃ - x₂/2 = 9/8`: the curvature of the trajectory from
`-e₁` points the way `N` cannot reach.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed enclosure misses a point of the time-interval reachable set

## References

* [1] [M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
      Krylov Subspace". IEEE Transactions on Automatic Control,
      2020.](../../../../../../references/2020/althoff-tac-krylov.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace
open scoped Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exponential of a matrix with `A³ = 0` is its Taylor polynomial of degree two. -/
private theorem Krylov.aux_exp_smul_of_pow_three {n : ℕ} (A : Mat ℝ n n) (hA : A ^ 3 = 0)
    (s : ℝ) : -- --- CONCL ---
    exp (s • A) = 1 + s • A + (s ^ 2 / 2) • A ^ 2 := by -- --- PROOF ---
  rw [Real.exp_smul_tsum, tsum_eq_sum (s := Finset.range 3)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial,
      Nat.cast_one, inv_one, pow_zero, one_mul, one_smul, pow_one, Nat.succ_eq_add_one]
    norm_num
    module
  · intro i hi
    have h3 : 3 ≤ i := by simpa using hi
    have hAi : A ^ i = 0 := by rw [show i = 3 + (i - 3) by omega, pow_add, hA, zero_mul]
    rw [hAi, smul_zero]

/-- The Hessenberg entries of the `3 × 3` shift's Arnoldi run at `e₁`, for all indices at once. -/
private theorem Krylov.aux_arnoldi_shift_hessenberg (i j : ℕ) :
    (Krylov.arnoldi (!![0, 0, 0; 1, 0, 0; 0, 1, 0] : Mat ℝ 3 3) ![1, 0, 0] 3).2 i j
      = if (j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 2) then 1 else 0 := by
  simp [Krylov.arnoldi, Krylov.gramSchmidtStep, norm₂, Fin.sum_univ_three, dotProduct, vecHead,
    vecTail]
  split_ifs <;> first | rfl | (exfalso; omega)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. III.2] as printed fails at the `3 × 3` shift, `X₀ = (e₃, e₁)`, `δ = 1`, `η = 2`:
Alg. 1 is exact (`h_{ξ+1,ξ} = 0`, so `ε_norm = 0`), and `e^{A/2}(e₃ - e₁)` is outside. -/
theorem Krylov.printed_time_interval_counterexample : -- --- CONCL ---
    let A : Mat ℝ 3 3 := !![0, 0, 0; 1, 0, 0; 0, 1, 0]
    let c : Vec ℝ 3 := ![0, 0, 1]
    let g : Vec ℝ 3 := ![1, 0, 0]
    let Kc := Krylov.arnoldi A c 1
    let Kg := Krylov.arnoldi A g 3
    let Vc : Mat ℝ 3 1 := Matrix.of fun i j => Kc.1 j i
    let Hc : Mat ℝ 1 1 := Matrix.of fun i j => Kc.2 i j
    let Vg : Mat ℝ 3 3 := Matrix.of fun i j => Kg.1 j i
    let Hg : Mat ℝ 3 3 := Matrix.of fun i j => Kg.2 i j
    let εnorm : ℝ := 0
    let X₀ : Set (Vec ℝ 3) := {x | ∃ β : ℝ, |β| ≤ 1 ∧ x = c + β • g}
    let Rδ : Set (Vec ℝ 3) := {y | ∃ β : ℝ, |β| ≤ 1 ∧ ∃ r : Vec ℝ 3,
      (∀ j, |r j| ≤ (‖c‖₂ + ‖g‖₂) * εnorm * 1) ∧
      y = ‖c‖₂ • (Vc *ᵥ (exp ((1 : ℝ) • Hc) *ᵥ Pi.single 0 1))
        + β • (‖g‖₂ • (Vg *ᵥ (exp ((1 : ℝ) • Hg) *ᵥ Pi.single 0 1))) + r}
    let N : Set (Vec ℝ 3) := {z | ∃ Fc ∈ Krylov.correctionSet Hc 1 2,
      ∃ Fg ∈ Krylov.correctionSet Hg 1 2,
        z = ‖c‖₂ • (Vc *ᵥ (Fc *ᵥ Pi.single 0 1)) + ‖g‖₂ • (Vg *ᵥ (Fg *ᵥ Pi.single 0 1))}
    (Kc.2 1 0 = 0 ∧ Kg.2 3 2 = 0)
      ∧ exp ((1 / 2 : ℝ) • A) *ᵥ (c - g) ∉ convexHull ℝ (X₀ ∪ Rδ) + N := by -- --- PROOF ---
  intro A c g Kc Kg Vc Hc Vg Hg εnorm X₀ Rδ N
  -- Alg. 1 at `e₃` breaks down at once, at `e₁` it runs through `e₁, e₂, e₃` with `H = A`
  have hnc : ‖c‖₂ = 1 := by simp [c, norm₂, Fin.sum_univ_three]
  have hng : ‖g‖₂ = 1 := by simp [g, norm₂, Fin.sum_univ_three]
  have hKc0 : Kc.1 0 = c := by simp [Kc, Krylov.arnoldi, hnc]
  have hKc : Kc.2 0 0 = 0 ∧ Kc.2 1 0 = 0 := by
    simp [Kc, Krylov.arnoldi, Krylov.gramSchmidtStep, A, c, norm₂, Fin.sum_univ_three,
      dotProduct, vecHead, vecTail]
  have hKg : Kg.1 0 = g ∧ Kg.1 1 = ![0, 1, 0] ∧ Kg.1 2 = ![0, 0, 1] := by
    simp [Kg, Krylov.arnoldi, Krylov.gramSchmidtStep, A, g, norm₂, Fin.sum_univ_three,
      dotProduct, vecHead, vecTail]
    funext i
    fin_cases i <;> rfl
  have hKg2 : ∀ i j : ℕ, Kg.2 i j = if (j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 2) then 1 else 0 :=
    Krylov.aux_arnoldi_shift_hessenberg
  have hHg : Hg = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Hg, hKg2, A]
  have hKg32 : Kg.2 3 2 = 0 := by simp [hKg2]
  -- so `V(e₁) = I`, `V(e₃) = e₃`, `H(e₃) = 0`, and `e^{sA} = I + sA + s²A²/2`
  have hVg : Vg = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Vg, hKg.1, hKg.2.1, hKg.2.2, g]
  have hVc : ∀ i, Vc i 0 = c i := fun i => by simp [Vc, hKc0]
  have hHc : Hc = 0 := by
    ext i j
    fin_cases i; fin_cases j
    simp [Hc, hKc.1]
  have hA3 : A ^ 3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  have hexpA := Krylov.aux_exp_smul_of_pow_three A hA3
  -- the functional `ℓ x = x₃ - x₂/2`, equal to `1` on `X₀` and on `R_h(1)`
  set ℓ : Vec ℝ 3 → ℝ := fun x => x 2 - x 1 / 2 with hℓ
  have hℓlin : IsLinearMap ℝ ℓ :=
    ⟨fun x y => by simp only [ℓ, Pi.add_apply]; ring,
      fun a x => by simp only [ℓ, Pi.smul_apply, smul_eq_mul]; ring⟩
  have hX : ∀ x ∈ X₀ ∪ Rδ, ℓ x = 1 := by
    rintro x (⟨β, -, rfl⟩ | ⟨β, -, r, hr, rfl⟩)
    · simp [ℓ, c, g]
    · have hr0 : r = 0 := funext fun j => abs_nonpos_iff.1 (by simpa [εnorm] using hr j)
      rw [hr0, hHc, hVg, hHg, hexpA, smul_zero, exp_zero]
      simp [ℓ, hnc, hng, hVc, mulVec, dotProduct, A, c, sq]
      ring
  -- the remainders `E` vanish: `|H|³ = 0` at `g`, and `H = 0` at `c`
  have hW0 : MatExp.expRemainderMat (0 : Mat ℝ 1 1) 1 2 = 0 := by
    have habs : MatExp.absMat (0 : Mat ℝ 1 1) = 0 := by
      ext i j
      simp [MatExp.absMat]
    simp [MatExp.expRemainderMat, habs, MatExp.expTaylor, Finset.sum_range_succ]
  have hWA : MatExp.expRemainderMat A 1 2 = 0 := by
    have habs : MatExp.absMat A = A := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [MatExp.absMat, A]
    rw [MatExp.expRemainderMat, habs, hexpA, MatExp.expTaylor]
    simp [Finset.sum_range_succ]
  -- `N` holds `λ₂ e₃/2`, `λ₂ ≤ 0`, so `ℓ ≤ 0` on it
  have hN : ∀ z ∈ N, ℓ z ≤ 0 := by
    rintro z ⟨Fc, hFc, Fg, hFg, rfl⟩
    rw [hHc] at hFc
    rw [hHg] at hFg
    obtain ⟨lc, Ec, -, hEc, rfl⟩ := hFc
    obtain ⟨lg, Eg, hlg, hEg, rfl⟩ := hFg
    have hEc0 : Ec = 0 := by
      ext i j
      exact abs_nonpos_iff.1 (by simpa [hW0] using hEc i j)
    have hEg0 : Eg = 0 := by
      ext i j
      exact abs_nonpos_iff.1 (by simpa [hWA] using hEg i j)
    have hl : lg 2 ≤ 0 := (hlg 2 (by simp)).2
    rw [hEc0, hEg0, hVg]
    simp [ℓ, Finset.Icc_self, hnc, hng, mulVec, dotProduct, A, sq]
    linarith
  -- the point `e^{A/2}(e₃ - e₁) = (-1, -1/2, 7/8)` has `ℓ = 9/8`
  have hq : ℓ (exp ((1 / 2 : ℝ) • A) *ᵥ (c - g)) = 9 / 8 := by
    rw [hexpA]
    simp [ℓ, A, c, g, mulVec, dotProduct, Fin.sum_univ_three, sq]
    norm_num
  refine ⟨⟨hKc.2, hKg32⟩, fun hmem => ?_⟩
  obtain ⟨p, hp, z, hz, hpz⟩ := Set.mem_add.1 hmem
  have hp1 : ℓ p = 1 := convexHull_min (fun x hx => hX x hx) (convex_hyperplane hℓlin 1) hp
  rw [← hpz, hℓlin.map_add, hp1] at hq
  linarith [hN z hz]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
