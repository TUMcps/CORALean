module

public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsConstructIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLast
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadRight

@[expose] public section

/-!
# A weighted block meets the weighted constraints, on the right

The mirror of the left one, at the complementary weight `(1 - t) / 2`: the same
three row groups, each reading the second block, and the weighting column
entering with the other sign.

## Inputs
* `P` – H-polytope
* `y` – vector of length `n₂`
* `z` – point of length `n₁`
* `w` – real number
* `t` – real number

## Hypotheses
* `hw` – `(1 - t) / 2 = w`
* `hw0` – `0 ≤ w`
* `hw1` – `w ≤ 1`
* `hy` – `y` lies in `P.nominal`

## Conclusion
* A weighted block meets the weighted constraints, on the right
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.smul_mem_halfScaledRight {P : HPolytope 𝕋 (Vec 𝕋 n₂)} {y : Vec ℝ n₂}
    {z : Vec ℝ n₁} {w t : ℝ} (hw : (1 - t) / 2 = w) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hy : y ∈ P.nominal.construct) : -- --- CONCL ---
    Fin.append (Fin.append z (w • y)) (fun _ : Fin 1 => t)
      ∈ (HPolytope.halfScaledRight n₁ P).construct := by -- --- PROOF ---
  obtain ⟨hle, heq⟩ := HPolytope.mem_nominal_iff.mp hy
  -- the third row group is the equality's lower end, which enters negated
  have hneg : toRealMat (fun i => -P.Ae i) = -toRealMat P.Ae := toRealMat_neg P.Ae
  rw [HPolytope.halfScaledRight, HPolytope.mem_stackRows_iff, HPolytope.mem_stackRows_nominal_iff]
  refine ⟨?_, ?_, ?_⟩ <;> rw [HPolytope.mem_nominal_iff] <;> refine ⟨fun i => ?_, fun i => i.elim0⟩
  -- an inequality row: its own bound, times a weight at most one, its slack read once
  · show (toRealMat (fun i => Fin.append (Fin.append (fun _ : Fin n₁ => FloatOps.zero) (P.A i))
        fun _ : Fin 1 => half (P.b i)) *ᵥ _) i
      ≤ toReal (half (P.b i)) + |toReal (P.b_error i)|
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append,
      Matrix.mulVec_smul, toReal_half]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hmul : w * (toRealMat P.A *ᵥ y) i ≤ w * (toReal (P.b i) + |toReal (P.b_error i)|) :=
      mul_le_mul_of_nonneg_left (hle i) hw0
    have hs : w * |toReal (P.b_error i)| ≤ |toReal (P.b_error i)| :=
      mul_le_of_le_one_left (abs_nonneg _) hw1
    have hkey : w * toReal (P.b i) + toReal (P.b i) / 2 * t = toReal (P.b i) / 2 := by
      rw [← hw]; ring
    linarith [mul_add w (toReal (P.b i)) |toReal (P.b_error i)|]
  -- an equality row: its right-hand side, times the weight, within the slack
  · show (toRealMat (fun i => Fin.append (Fin.append (fun _ : Fin n₁ => FloatOps.zero) (P.Ae i))
        fun _ : Fin 1 => half (P.be i)) *ᵥ _) i
      ≤ toReal (half (P.be i)) + |toReal (P.be_error i)|
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append,
      Matrix.mulVec_smul, toReal_half]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hab := abs_le.mp (heq i)
    have hmul : w * (toRealMat P.Ae *ᵥ y) i ≤ w * (toReal (P.be i) + |toReal (P.be_error i)|) :=
      mul_le_mul_of_nonneg_left (by linarith [hab.2]) hw0
    have hs : w * |toReal (P.be_error i)| ≤ |toReal (P.be_error i)| :=
      mul_le_of_le_one_left (abs_nonneg _) hw1
    have hkey : w * toReal (P.be i) + toReal (P.be i) / 2 * t = toReal (P.be i) / 2 := by
      rw [← hw]; ring
    linarith [mul_add w (toReal (P.be i)) |toReal (P.be_error i)|]
  -- and the same row negated, where the weight multiplies the right-hand side the other way
  · show (toRealMat (fun i => Fin.append (Fin.append (fun _ : Fin n₁ => FloatOps.zero) (-(P.Ae i)))
        fun _ : Fin 1 => half (neg (P.be i))) *ᵥ _) i
      ≤ toReal (half (neg (P.be i))) + |toReal (P.be_error i)|
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append, hneg,
      Matrix.neg_mulVec, Matrix.mulVec_smul, toReal_half, toReal_neg]
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    have hab := abs_le.mp (heq i)
    have hmul : w * (toReal (P.be i) - |toReal (P.be_error i)|) ≤ w * (toRealMat P.Ae *ᵥ y) i :=
      mul_le_mul_of_nonneg_left (by linarith [hab.1]) hw0
    have hs : w * |toReal (P.be_error i)| ≤ |toReal (P.be_error i)| :=
      mul_le_of_le_one_left (abs_nonneg _) hw1
    have hkey : w * toReal (P.be i) + toReal (P.be i) / 2 * t = toReal (P.be i) / 2 := by
      rw [← hw]; ring
    linarith [mul_sub w (toReal (P.be i)) |toReal (P.be_error i)|]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
