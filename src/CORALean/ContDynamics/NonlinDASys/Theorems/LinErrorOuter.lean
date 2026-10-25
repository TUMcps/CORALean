module

public import CORALean.ContDynamics.NonlinDASys.Operations.LinError
public import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import Mathlib.Data.Matrix.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `linError` holds the linearization error at every Hessian of the intervals

[1, Cor. 1]: `{½ (σ - CF⁻¹φ) | σᵢ = νᵀHᵈ⁽ⁱ⁾ν, φⱼ = νᵀHᵃ⁽ʲ⁾ν, ν ∈ R^z_Δ} ⊆ L_c ⊕ L_Δ` for every
`Hᵈ⁽ⁱ⁾`, `Hᵃ⁽ʲ⁾` in their intervals. Each row may take its own matrix, so this holds the set of
[1, Eq. 15] whether its Hessians are taken at one `ξ` for all rows, as printed, or at one `ξ` per
row, as [1, Eq. 8] gives them. By the printed proof. The midpoint part: `σ_c - CF⁻¹φ_c` is the
quadratic map of the one family `Hᵈ_c⁽ⁱ⁾ - Σⱼ (CF⁻¹)ᵢⱼ Hᵃ_c⁽ʲ⁾` at `ν`, which [1, Lemma 1] encloses.
The radius part: `|νᵀ(Hᵈ⁽ⁱ⁾ - Hᵈ_c⁽ⁱ⁾)ν| ≤ |ν|ᵀHᵈ_Δ⁽ⁱ⁾|ν| ≤ ζᵢ` as in [1, Thm. 1]. The printed proof
ends with `L_c ⊆ (d + CF⁻¹e, H + CF⁻¹V)`, the sign flipped against the statement; the
statement's `-` is what holds.

## Inputs
* `Hd_c` – dynamics Hessian midpoints
* `Hd_Δ` – dynamics Hessian radii
* `Ha_c` – constraint Hessian midpoints
* `Ha_Δ` – constraint Hessian radii
* `CF_inv` – the matrix `C F⁻¹`
* `R_Δ` – deviation zonotope
* `Hd` – dynamics Hessian rows
* `Ha` – constraint Hessian rows
* `ν` – deviation

## Hypotheses
* `hHd` – dynamics Hessians within their intervals
* `hHa` – constraint Hessians within their intervals
* `hν` – `ν` lies in the deviation zonotope

## Conclusion
* the quadratic-form error lies in the linearization error set

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An entrywise bound `S` on `E` bounds the quadratic form at anything `a` covers. -/
theorem NonlinDASys.aux_linError_abs_quad_le {E S : Mat ℝ q q} {x a : Vec ℝ q}
    (hE : ∀ j k, |E j k| ≤ S j k) (hx : ∀ j, |x j| ≤ a j) : -- --- CONCL ---
    |x ⬝ᵥ (E *ᵥ x)| ≤ a ⬝ᵥ (S *ᵥ a) := by -- --- PROOF ---
  have ha : ∀ j, 0 ≤ a j := fun j => (abs_nonneg _).trans (hx j)
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  -- three factors, each replaced by what bounds it
  rw [abs_mul, abs_mul]
  exact mul_le_mul (hx j) (mul_le_mul (hE j k) (hx k) (abs_nonneg _)
    ((abs_nonneg _).trans (hE j k))) (by positivity) (ha j)

/-- `xᵀ(A - Σⱼ Mᵢⱼ Bⱼ)y = xᵀAy - Σⱼ Mᵢⱼ xᵀBⱼy`: the quadratic form is linear in the matrix. -/
theorem NonlinDASys.aux_linError_form_sub (A : Mat ℝ q q) (B : Fin p → Mat ℝ q q)
    (M : Mat ℝ n p) (i : Fin n) (x y : Vec ℝ q) :
    x ⬝ᵥ ((A - ∑ j, M i j • B j) *ᵥ y) = x ⬝ᵥ (A *ᵥ y) - ∑ j, M i j * (x ⬝ᵥ (B j *ᵥ y)) := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The center of `quad(Hᵈ_c - CF⁻¹Hᵃ_c, R)` is `d - CF⁻¹e`. -/
theorem NonlinDASys.aux_linError_quadMap_sub_c (Hd : Fin n → Mat ℝ q q)
    (Ha : Fin p → Mat ℝ q q) (M : Mat ℝ n p) (R : Zonotope (Vec ℝ q)) : -- --- CONCL ---
    (R.quadMap (fun i => Hd i - ∑ j, M i j • Ha j)).c
      = (R.quadMap Hd).c - M *ᵥ (R.quadMap Ha).c := by -- --- PROOF ---
  have hmv : ∀ (v : Vec ℝ p) i, (M *ᵥ v) i = ∑ j, M i j * v j := fun v i => rfl
  funext i
  simp only [Zonotope.quadMap, Pi.sub_apply, hmv, NonlinDASys.aux_linError_form_sub (Hd i) Ha M i]
  -- the generator sum and the sum over the rows of `CF⁻¹` commute
  have hswap : ∑ s, (R.G s ⬝ᵥ (Hd i *ᵥ R.G s) - ∑ j, M i j * (R.G s ⬝ᵥ (Ha j *ᵥ R.G s)))
      = ∑ s, R.G s ⬝ᵥ (Hd i *ᵥ R.G s) - ∑ j, M i j * ∑ s, R.G s ⬝ᵥ (Ha j *ᵥ R.G s) := by
    rw [Finset.sum_sub_distrib, Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hhalf : ∑ j, M i j * (R.c ⬝ᵥ (Ha j *ᵥ R.c) + 1 / 2 * ∑ s, R.G s ⬝ᵥ (Ha j *ᵥ R.G s))
      = ∑ j, M i j * R.c ⬝ᵥ (Ha j *ᵥ R.c)
        + 1 / 2 * ∑ j, M i j * ∑ s, R.G s ⬝ᵥ (Ha j *ᵥ R.G s) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hswap, hhalf]
  ring

/-- The generators of `quad(Hᵈ_c - CF⁻¹Hᵃ_c, R)` are `H - CF⁻¹V`, block by block. -/
theorem NonlinDASys.aux_linError_quadMap_sub_G (Hd : Fin n → Mat ℝ q q)
    (Ha : Fin p → Mat ℝ q q) (M : Mat ℝ n p) (R : Zonotope (Vec ℝ q))
    (l : Fin (R.h + R.h + R.h * R.h)) : -- --- CONCL ---
    (R.quadMap (fun i => Hd i - ∑ j, M i j • Ha j)).G l
      = (R.quadMap Hd).G l - M *ᵥ (R.quadMap Ha).G l := by -- --- PROOF ---
  have hmv : ∀ (v : Vec ℝ p) i, (M *ᵥ v) i = ∑ j, M i j * v j := fun v i => rfl
  funext i
  simp only [Zonotope.quadMap, Pi.sub_apply, hmv]
  have hf := NonlinDASys.aux_linError_form_sub (Hd i) Ha M i
  induction l using Fin.addCases with
  | left l =>
    induction l using Fin.addCases with
    -- the linear generators
    | left l =>
      simp only [Fin.append_left, hf, mul_add, Finset.sum_add_distrib]
      ring
    -- the squares
    | right l =>
      simp only [Fin.append_left, Fin.append_right, hf]
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring
  -- the pairs, zero off `j < k` on both sides
  | right l =>
    simp only [Fin.append_right]
    split_ifs
    · simp only [hf, mul_add, Finset.sum_add_distrib]
      ring
    · simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 1]: `½ (σ - CF⁻¹φ) ∈ L_c ⊕ L_Δ`, `σᵢ = νᵀHᵈ⁽ⁱ⁾ν`, `φⱼ = νᵀHᵃ⁽ʲ⁾ν`, for every
`ν ∈ R^z_Δ` and every `Hᵈ⁽ⁱ⁾`, `Hᵃ⁽ʲ⁾` in their intervals. -/
theorem NonlinDASys.linError_outer (Hd_c Hd_Δ : Fin n → Mat ℝ q q)
    (Ha_c Ha_Δ : Fin p → Mat ℝ q q) (CF_inv : Mat ℝ n p) (R_Δ : Zonotope (Vec ℝ q))
    {Hd : Fin n → Mat ℝ q q} {Ha : Fin p → Mat ℝ q q}
    (hHd : ∀ i j k, |Hd i j k - Hd_c i j k| ≤ Hd_Δ i j k)
    (hHa : ∀ i j k, |Ha i j k - Ha_c i j k| ≤ Ha_Δ i j k) {ν : Vec ℝ q}
    (hν : ν ∈ R_Δ.construct) : -- --- CONCL ---
    (1 / 2 : ℝ) • ((fun i => ν ⬝ᵥ (Hd i *ᵥ ν)) - CF_inv *ᵥ (fun j => ν ⬝ᵥ (Ha j *ᵥ ν)))
      ∈ (NonlinDASys.linError Hd_c Hd_Δ Ha_c Ha_Δ CF_inv R_Δ).construct := by -- --- PROOF ---
  set σc : Vec ℝ n := fun i => ν ⬝ᵥ (Hd_c i *ᵥ ν) with hσc
  set φc : Vec ℝ p := fun j => ν ⬝ᵥ (Ha_c j *ᵥ ν) with hφc
  -- [1, Lemma 1] at the one family `Hᵈ_c - CF⁻¹Hᵃ_c`: one set of factors for `σ_c` and `φ_c`
  obtain ⟨β, hβ, hβeq⟩ := Zonotope.quadMap_outer
    (fun i => Hd_c i - ∑ j, CF_inv i j • Ha_c j) R_Δ ⟨ν, hν, rfl⟩
  have hmid : (fun i => ν ⬝ᵥ ((Hd_c i - ∑ j, CF_inv i j • Ha_c j) *ᵥ ν))
      = σc - CF_inv *ᵥ φc := by
    funext i
    rw [NonlinDASys.aux_linError_form_sub]
    rfl
  replace hβeq := hmid.symm.trans hβeq
  -- the radius parts, each in its box by the entrywise bound
  obtain ⟨γ, hγ, hνγ⟩ := Zonotope.mem_construct_iff.mp hν
  have hbox : ∀ {k : ℕ} (H H_c H_Δ : Fin k → Mat ℝ q q),
      (∀ i j l, |H i j l - H_c i j l| ≤ H_Δ i j l) →
      (fun i => ν ⬝ᵥ ((H i - H_c i) *ᵥ ν)) ∈ (Interval.zonotope
        ⟨-(fun i => R_Δ.absBound ⬝ᵥ (H_Δ i *ᵥ R_Δ.absBound)),
          fun i => R_Δ.absBound ⬝ᵥ (H_Δ i *ᵥ R_Δ.absBound)⟩).construct := by
    intro k H H_c H_Δ hH
    refine Interval.zonotope_contains _ fun i => ?_
    exact abs_le.mp (NonlinDASys.aux_linError_abs_quad_le (fun j l => by simpa using hH i j l)
      (Zonotope.abs_le_absBound hγ hνγ))
  simp only [NonlinDASys.linError]
  rw [← Zonotope.plus_exact]
  refine ⟨(1 / 2 : ℝ) • (σc - CF_inv *ᵥ φc), ⟨β, hβ, ?_⟩,
    (1 / 2 : ℝ) • ((fun i => ν ⬝ᵥ ((Hd i - Hd_c i) *ᵥ ν))
      - CF_inv *ᵥ (fun j => ν ⬝ᵥ ((Ha j - Ha_c j) *ᵥ ν))), ?_, ?_⟩
  -- the midpoint part: `L_c`'s center and generators are half those of the one family
  · rw [hβeq, NonlinDASys.aux_linError_quadMap_sub_c]
    simp only [smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by
      rw [NonlinDASys.aux_linError_quadMap_sub_G Hd_c Ha_c CF_inv R_Δ l, smul_comm]
  -- the radius part: `½ (σ_Δ + (-CF⁻¹) φ_Δ)`, a point of `½ ([-ζ, ζ] ⊕ (-CF⁻¹)[-ϱ, ϱ])`
  · rw [← Zonotope.mtimes_exact]
    refine ⟨(fun i => ν ⬝ᵥ ((Hd i - Hd_c i) *ᵥ ν))
      + (-CF_inv) *ᵥ (fun j => ν ⬝ᵥ ((Ha j - Ha_c j) *ᵥ ν)), ?_, ?_⟩
    · rw [← Zonotope.plus_exact]
      refine Set.add_mem_add (hbox Hd Hd_c Hd_Δ hHd) ?_
      rw [← Zonotope.mtimes_exact]
      exact Set.mem_image_of_mem _ (hbox Ha Ha_c Ha_Δ hHa)
    · beta_reduce
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, ← sub_eq_add_neg]
  -- the two parts add up to `½ (σ - CF⁻¹φ)`
  · have hσ : (fun i => ν ⬝ᵥ ((Hd i - Hd_c i) *ᵥ ν)) = (fun i => ν ⬝ᵥ (Hd i *ᵥ ν)) - σc := by
      funext i; simp [Matrix.sub_mulVec, dotProduct_sub, hσc]
    have hφ : (fun j => ν ⬝ᵥ ((Ha j - Ha_c j) *ᵥ ν)) = (fun j => ν ⬝ᵥ (Ha j *ᵥ ν)) - φc := by
      funext j; simp [Matrix.sub_mulVec, dotProduct_sub, hφc]
    rw [hσ, hφ, Matrix.mulVec_sub]
    module

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
