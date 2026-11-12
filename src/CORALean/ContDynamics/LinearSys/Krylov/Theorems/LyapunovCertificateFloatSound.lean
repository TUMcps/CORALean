module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.LyapunovCertificateFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.QuadLeQuadBoundUp
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# An accepted Lyapunov weight is symmetric, bounded and has its rate

`Krylov.lyapunovCertificateFloat` accepts a float weight `P` when the outward-rounded products
`L*L` and `PA` leave `E = P - aI - L*L` and `W = PA + (PA)* + I` small in Gershgorin's sense. Then
`P` is symmetric, `x*Px` lies between `lower·x*x` and `upper·x*x` with `lower > 0`, and `x*PAx ≤
rate · x*Px`. The first because `x*Px = a x*x + ‖Lx‖² + x*Ex`, the last because `2x*PAx = x*Wx -
x*x` and `x*Wx` is at most Gershgorin's bound of the entrywise absolute value of `W`, which
`Krylov.quad_le_quadBoundUp` bounds for the vector `|x|` ([1, Eq. 3.4] bounds the growth by such a
form).

## Inputs
* `A` – matrix
* `P` – symmetric weight
* `L` – factor of `P - aI`
* `a` – shift

## Hypotheses
* `hok` – the weight was accepted

## Conclusion
* the weight is symmetric, its quadratic form is within the bounds, and the rate holds

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix within the entries of `C` has its quadratic form within Gershgorin's bound of `C`. -/
private theorem aux_abs_quad_le {k : ℕ} (B : Mat ℝ k k) (C : Mat 𝕋 k k)
    (hB : ∀ i j, |B i j| ≤ toReal (C i j)) (x : Vec ℝ k) : -- --- CONCL ---
    |x ⬝ᵥ (B *ᵥ x)| ≤ toReal (Krylov.quadBoundUp C) * (x ⬝ᵥ x) := by -- --- PROOF ---
  have h := Krylov.quad_le_quadBoundUp C (fun i => |x i|)
  have hxx : (fun i => |x i|) ⬝ᵥ (fun i => |x i|) = x ⬝ᵥ x := by
    simp only [dotProduct, ← sq, sq_abs]
  rw [hxx] at h
  refine le_trans ?_ h
  simp only [dotProduct, mulVec, toRealMat]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => ?_)) (abs_nonneg _)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hB i j) (abs_nonneg _)

/-- A real between two bounds has its absolute value below the larger absolute bound. -/
private theorem aux_abs_le_max {x lo hi : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    |x| ≤ max |lo| |hi| := by
  have := le_max_left |lo| |hi|
  have := le_max_right |lo| |hi|
  rw [abs_le]
  constructor <;> linarith [neg_abs_le lo, le_abs_self hi]

/-- `E = P - aI - L*L` lies entrywise within the bound the check forms from the rounded products. -/
private theorem aux_entry_E (P L : Mat 𝕋 n n) (a : 𝕋) (i j : Fin n) : -- --- CONCL ---
    |(toRealMat P - toReal a • (1 : Mat ℝ n n) - (toRealMat L)ᵀ * toRealMat L) i j| ≤
      toReal (maximum (absolute (subDown (subDown (P i j) (if i = j then a else FloatOps.zero))
        (matMulUp (fun i j => L j i) L i j)))
        (absolute (subUp (subUp (P i j) (if i = j then a else FloatOps.zero))
          (matMulDown (fun i j => L j i) L i j)))) := by -- --- PROOF ---
  have hd : toReal (if i = j then a else (FloatOps.zero : 𝕋)) =
      toReal a * (if i = j then 1 else 0) := by
    split_ifs <;> simp [toReal_zero]
  have hup : ∑ l, toReal (L l i) * toReal (L l j) ≤ toReal (matMulUp (fun i j => L j i) L i j) :=
    le_dotUp (fun l => L l i) (fun l => L l j)
  have hdn : toReal (matMulDown (fun i j => L j i) L i j) ≤ ∑ l, toReal (L l i) * toReal (L l j) :=
    dotDown_le (fun l => L l i) (fun l => L l j)
  -- the rounded-down and rounded-up differences enclose the exact entry
  have h1 := subDown_le_sub (subDown (P i j) (if i = j then a else FloatOps.zero))
    (matMulUp (fun i j => L j i) L i j)
  have h2 := subDown_le_sub (P i j) (if i = j then a else FloatOps.zero)
  have h3 := sub_le_subUp (subUp (P i j) (if i = j then a else FloatOps.zero))
    (matMulDown (fun i j => L j i) L i j)
  have h4 := sub_le_subUp (P i j) (if i = j then a else FloatOps.zero)
  rw [hd] at h2 h4
  rw [toReal_maximum, toReal_absolute, toReal_absolute]
  refine aux_abs_le_max ?_ ?_
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.transpose_apply, smul_eq_mul, toRealMat]
    linarith
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.transpose_apply, smul_eq_mul, toRealMat]
    linarith

/-- `W = PA + (PA)* + I` lies entrywise within the bound the check forms from the rounded
products. -/
private theorem aux_entry_W (A P : Mat 𝕋 n n) (i j : Fin n) : -- --- CONCL ---
    |(toRealMat P * toRealMat A + (toRealMat P * toRealMat A)ᵀ + 1) i j| ≤
      toReal (maximum (absolute (addDown (addDown (matMulDown P A i j) (matMulDown P A j i))
        (if i = j then FloatOps.one else FloatOps.zero)))
        (absolute (addUp (addUp (matMulUp P A i j) (matMulUp P A j i))
          (if i = j then FloatOps.one else FloatOps.zero)))) := by -- --- PROOF ---
  have hd : toReal (if i = j then (FloatOps.one : 𝕋) else FloatOps.zero) =
      (if i = j then 1 else 0) := by
    split_ifs <;> simp [toReal_zero, toReal_one]
  have hup : ∀ i j, ∑ l, toReal (P i l) * toReal (A l j) ≤ toReal (matMulUp P A i j) :=
    fun i j => le_dotUp (P i) (fun l => A l j)
  have hdn : ∀ i j, toReal (matMulDown P A i j) ≤ ∑ l, toReal (P i l) * toReal (A l j) :=
    fun i j => dotDown_le (P i) (fun l => A l j)
  -- the rounded-down and rounded-up sums enclose the exact entry
  have h1 := addDown_le_add (addDown (matMulDown P A i j) (matMulDown P A j i))
    (if i = j then FloatOps.one else FloatOps.zero)
  have h2 := addDown_le_add (matMulDown P A i j) (matMulDown P A j i)
  have h3 := add_le_addUp (addUp (matMulUp P A i j) (matMulUp P A j i))
    (if i = j then FloatOps.one else FloatOps.zero)
  have h4 := add_le_addUp (matMulUp P A i j) (matMulUp P A j i)
  rw [hd] at h1 h3
  have e1 := hup i j
  have e2 := hup j i
  have e3 := hdn i j
  have e4 := hdn j i
  rw [toReal_maximum, toReal_absolute, toReal_absolute]
  refine aux_abs_le_max ?_ ?_
  · simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.mul_apply, Matrix.one_apply,
      toRealMat]
    linarith
  · simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.mul_apply, Matrix.one_apply,
      toRealMat]
    linarith

/-- `x*Px = a x*x + ‖Lx‖² + x*Ex ≥ (a - ρ_E) x*x`. -/
private theorem aux_lower (P L : Mat 𝕋 n n) (a : 𝕋) (C : Mat 𝕋 n n)
    (hE : ∀ i j, |(toRealMat P - toReal a • (1 : Mat ℝ n n) - (toRealMat L)ᵀ * toRealMat L) i j| ≤
      toReal (C i j)) (x : Vec ℝ n) : -- --- CONCL ---
    toReal (subDown a (Krylov.quadBoundUp C)) * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (toRealMat P *ᵥ x) := by -- --- PROOF ---
  have hLt : ∀ x w : Vec ℝ n, x ⬝ᵥ ((toRealMat L)ᵀ *ᵥ w) = (toRealMat L *ᵥ x) ⬝ᵥ w :=
    fun x w => by rw [dotProduct_mulVec, vecMul_transpose]
  have hnn : ∀ x : Vec ℝ n, 0 ≤ x ⬝ᵥ x := fun x => Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h1 := (abs_le.1 (aux_abs_quad_le _ C hE x)).1
  have h2 : x ⬝ᵥ ((toRealMat P - toReal a • (1 : Mat ℝ n n) - (toRealMat L)ᵀ * toRealMat L) *ᵥ x) =
      x ⬝ᵥ (toRealMat P *ᵥ x) - toReal a * (x ⬝ᵥ x) -
        (toRealMat L *ᵥ x) ⬝ᵥ (toRealMat L *ᵥ x) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, dotProduct_sub, dotProduct_sub, dotProduct_smul, smul_eq_mul, hLt]
  have h3 := subDown_le_sub a (Krylov.quadBoundUp C)
  rw [h2] at h1
  nlinarith [h1, h3, hnn x, hnn (toRealMat L *ᵥ x)]

/-- `2x*PAx = x*Wx - x*x` bounds `x*PAx` by the rate times `x*Px`. -/
private theorem aux_rate (A P : Mat 𝕋 n n) (C : Mat 𝕋 n n)
    (hW : ∀ i j, |(toRealMat P * toRealMat A + (toRealMat P * toRealMat A)ᵀ + 1) i j| ≤
      toReal (C i j)) (hq : ∀ x : Vec ℝ n, 0 ≤ x ⬝ᵥ (toRealMat P *ᵥ x))
    (hg : 0 < toReal (subDown FloatOps.one (Krylov.quadBoundUp C)))
    (hu : 0 < toReal (Krylov.quadBoundUp P)) (x : Vec ℝ n) : -- --- CONCL ---
    x ⬝ᵥ (toRealMat P *ᵥ (toRealMat A *ᵥ x)) ≤
      toReal (neg (divDown (subDown FloatOps.one (Krylov.quadBoundUp C))
        (addUp (Krylov.quadBoundUp P) (Krylov.quadBoundUp P)))) *
        (x ⬝ᵥ (toRealMat P *ᵥ x)) := by -- --- PROOF ---
  have hT : ∀ (M : Mat ℝ n n) (x w : Vec ℝ n), x ⬝ᵥ (Mᵀ *ᵥ w) = (M *ᵥ x) ⬝ᵥ w :=
    fun M x w => by rw [dotProduct_mulVec, vecMul_transpose]
  have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h1 := (abs_le.1 (aux_abs_quad_le _ C hW x)).2
  have h2 : x ⬝ᵥ ((toRealMat P * toRealMat A + (toRealMat P * toRealMat A)ᵀ + 1) *ᵥ x) =
      2 * (x ⬝ᵥ (toRealMat P *ᵥ (toRealMat A *ᵥ x))) + x ⬝ᵥ x := by
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_add,
      hT, Matrix.mulVec_mulVec, dotProduct_comm ((toRealMat P * toRealMat A) *ᵥ x) x]
    ring
  rw [h2] at h1
  have h3 := subDown_le_sub FloatOps.one (Krylov.quadBoundUp C)
  rw [toReal_one] at h3
  have hqb := Krylov.quad_le_quadBoundUp P x
  have hq' : x ⬝ᵥ (toRealMat P *ᵥ (toRealMat A *ᵥ x)) ≤
      -(toReal (subDown FloatOps.one (Krylov.quadBoundUp C)) / 2) * (x ⬝ᵥ x) := by nlinarith
  -- the rate: its divisor is at least `2b`, so the quotient is below `gap/(2b)`
  have hden : 2 * toReal (Krylov.quadBoundUp P) ≤
      toReal (addUp (Krylov.quadBoundUp P) (Krylov.quadBoundUp P)) := by
    have := add_le_addUp (Krylov.quadBoundUp P) (Krylov.quadBoundUp P)
    linarith
  have hden0 : 0 < toReal (addUp (Krylov.quadBoundUp P) (Krylov.quadBoundUp P)) := by linarith
  have hrg := divDown_le_div (subDown FloatOps.one (Krylov.quadBoundUp C))
    (addUp (Krylov.quadBoundUp P) (Krylov.quadBoundUp P)) hden0
  -- against the rate, `x*Px` between `0` and `b x*x`
  have hrg2 : toReal (subDown FloatOps.one (Krylov.quadBoundUp C)) /
      toReal (addUp (Krylov.quadBoundUp P) (Krylov.quadBoundUp P)) ≤
      toReal (subDown FloatOps.one (Krylov.quadBoundUp C)) / (2 * toReal (Krylov.quadBoundUp P)) :=
    div_le_div_of_nonneg_left hg.le (by linarith) hden
  rw [toReal_neg]
  generalize toReal (divDown (subDown FloatOps.one (Krylov.quadBoundUp C))
    (addUp (Krylov.quadBoundUp P) (Krylov.quadBoundUp P))) = rg at hrg ⊢
  generalize toReal (subDown FloatOps.one (Krylov.quadBoundUp C)) = gap at *
  generalize toReal (Krylov.quadBoundUp P) = b at *
  have hrg3 : rg ≤ gap / (2 * b) := hrg.trans hrg2
  have hgb : 0 ≤ gap / (2 * b) := div_nonneg hg.le (by linarith)
  have hq0 := hq x
  have e1 : -(gap / (2 * b)) * (x ⬝ᵥ (toRealMat P *ᵥ x)) ≤ -rg * (x ⬝ᵥ (toRealMat P *ᵥ x)) := by
    nlinarith
  have e2 : -(gap / (2 * b)) * (b * (x ⬝ᵥ x)) ≤ -(gap / (2 * b)) * (x ⬝ᵥ (toRealMat P *ᵥ x)) := by
    nlinarith
  have e3 : -(gap / (2 * b)) * (b * (x ⬝ᵥ x)) = -(gap / 2) * (x ⬝ᵥ x) := by
    field_simp
  nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- An accepted weight is symmetric and has `a x*x ≤ x*Px ≤ b x*x`, `0 < a`, `0 < b` and
`x*PAx ≤ μ x*Px` for its `lower`, `upper` and `rate`. -/
theorem Krylov.lyapunovCertificateFloat_sound (A P L : Mat 𝕋 n n) (a : 𝕋)
    (hok : (Krylov.lyapunovCertificateFloat A P L a).ok = true) : -- --- CONCL ---
    (toRealMat P)ᵀ = toRealMat P ∧
    0 < toReal (Krylov.lyapunovCertificateFloat A P L a).lower ∧
    0 < toReal (Krylov.lyapunovCertificateFloat A P L a).upper ∧
    (∀ x : Vec ℝ n, toReal (Krylov.lyapunovCertificateFloat A P L a).lower * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (toRealMat P *ᵥ x)) ∧
    (∀ x : Vec ℝ n, x ⬝ᵥ (toRealMat P *ᵥ x) ≤
      toReal (Krylov.lyapunovCertificateFloat A P L a).upper * (x ⬝ᵥ x)) ∧
    (∀ x : Vec ℝ n, x ⬝ᵥ (toRealMat P *ᵥ (toRealMat A *ᵥ x)) ≤
      toReal (Krylov.lyapunovCertificateFloat A P L a).rate *
        (x ⬝ᵥ (toRealMat P *ᵥ x))) := by -- --- PROOF ---
  unfold Krylov.lyapunovCertificateFloat at hok ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hs, hl⟩, hg⟩, hu⟩ := hok
  simp only
  have hl' := toReal_lt_of_ltStrict hl
  have hg' := toReal_lt_of_ltStrict hg
  have hu' := toReal_lt_of_ltStrict hu
  rw [toReal_zero] at hl' hg' hu'
  -- symmetry
  have hsymm : (toRealMat P)ᵀ = toRealMat P := by
    ext i j
    exact le_antisymm (toReal_le_of_le (hs j i).1) (toReal_le_of_le (hs j i).2)
  have hlow := aux_lower P L a _ (fun i j => aux_entry_E P L a i j)
  have hnn : ∀ x : Vec ℝ n, 0 ≤ x ⬝ᵥ x := fun x => Finset.sum_nonneg fun i _ => mul_self_nonneg _
  refine ⟨hsymm, hl', hu', hlow, fun x => Krylov.quad_le_quadBoundUp P x, ?_⟩
  exact aux_rate A P _ (fun i j => aux_entry_W A P i j)
    (fun x => (mul_nonneg hl'.le (hnn x)).trans (hlow x)) hg' hu'

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
