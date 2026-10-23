module

public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledLeft
public import CORALean.ContSet.HPolytope.Float.Theorems.MemStackRowsConstructIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MulVecAppendLast
public import CORALean.ContSet.HPolytope.Float.Theorems.MulVecPadLeft

@[expose] public section

/-!
# A weighted block meets the weighted constraints, on the left

The direction a convex combination needs: a member of `P`, scaled by a
nonnegative weight and placed in the first block, satisfies the weighted rows
when the trailing coefficient names that same weight. Each row is its own bound
times the weight, and the halved right-hand side is what carries it.

Stated for the whole appended coefficient vector rather than for the block
alone: the weight multiplies the first block and not the second, so no
membership of the concatenation says it.

## Inputs
* `P` – H-polytope
* `y` – vector of length `n₁`
* `z` – point of length `n₂`
* `w` – real number
* `t` – real number

## Hypotheses
* `hw` – `(t + 1) / 2 = w`
* `hw0` – `0 ≤ w`
* `hw1` – `w ≤ 1`
* `hy` – `y` lies in `P.nominal`

## Conclusion
* A weighted block meets the weighted constraints, on the left
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

theorem HPolytope.smul_mem_halfScaledLeft {P : HPolytope 𝕋 (Vec 𝕋 n₁)} {y : Vec ℝ n₁}
    {z : Vec ℝ n₂} {w t : ℝ} (hw : (t + 1) / 2 = w) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hy : y ∈ P.nominal.construct) : -- --- CONCL ---
    Fin.append (Fin.append (w • y) z) (fun _ : Fin 1 => t)
      ∈ (P.halfScaledLeft n₂).construct := by -- --- PROOF ---
  obtain ⟨hle, heq⟩ := HPolytope.mem_nominal_iff.mp hy
  -- the third row group is the equality's lower end, which enters negated
  have hneg : toRealMat (fun i => -P.Ae i) = -toRealMat P.Ae := toRealMat_neg P.Ae
  rw [HPolytope.halfScaledLeft, HPolytope.mem_stackRows_iff, HPolytope.mem_stackRows_nominal_iff]
  refine ⟨?_, ?_, ?_⟩ <;> rw [HPolytope.mem_nominal_iff] <;> refine ⟨fun i => ?_, fun i => i.elim0⟩
  -- an inequality row: its own bound, times a weight at most one, its slack read once
  · show (toRealMat (fun i => Fin.append (Fin.append (P.A i) fun _ : Fin n₂ => FloatOps.zero)
        fun _ : Fin 1 => neg (half (P.b i))) *ᵥ _) i
      ≤ toReal (half (P.b i)) + |toReal (P.b_error i)|
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padLeft, blockLeft_append,
      Matrix.mulVec_smul, toReal_neg, toReal_half]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hmul : w * (toRealMat P.A *ᵥ y) i ≤ w * (toReal (P.b i) + |toReal (P.b_error i)|) :=
      mul_le_mul_of_nonneg_left (hle i) hw0
    have hs : w * |toReal (P.b_error i)| ≤ |toReal (P.b_error i)| :=
      mul_le_of_le_one_left (abs_nonneg _) hw1
    have hkey : w * toReal (P.b i) + -(toReal (P.b i) / 2) * t = toReal (P.b i) / 2 := by
      rw [← hw]; ring
    linarith [mul_add w (toReal (P.b i)) |toReal (P.b_error i)|]
  -- an equality row: its right-hand side, times the weight, within the slack
  · show (toRealMat (fun i => Fin.append (Fin.append (P.Ae i) fun _ : Fin n₂ => FloatOps.zero)
        fun _ : Fin 1 => neg (half (P.be i))) *ᵥ _) i
      ≤ toReal (half (P.be i)) + |toReal (P.be_error i)|
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padLeft, blockLeft_append,
      Matrix.mulVec_smul, toReal_neg, toReal_half]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hab := abs_le.mp (heq i)
    have hmul : w * (toRealMat P.Ae *ᵥ y) i ≤ w * (toReal (P.be i) + |toReal (P.be_error i)|) :=
      mul_le_mul_of_nonneg_left (by linarith [hab.2]) hw0
    have hs : w * |toReal (P.be_error i)| ≤ |toReal (P.be_error i)| :=
      mul_le_of_le_one_left (abs_nonneg _) hw1
    have hkey : w * toReal (P.be i) + -(toReal (P.be i) / 2) * t = toReal (P.be i) / 2 := by
      rw [← hw]; ring
    linarith [mul_add w (toReal (P.be i)) |toReal (P.be_error i)|]
  -- and the same row negated, where the weight multiplies the right-hand side the other way
  · show (toRealMat (fun i => Fin.append (Fin.append (-(P.Ae i)) fun _ : Fin n₂ => FloatOps.zero)
        fun _ : Fin 1 => neg (half (neg (P.be i)))) *ᵥ _) i
      ≤ toReal (half (neg (P.be i))) + |toReal (P.be_error i)|
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padLeft, blockLeft_append, hneg,
      Matrix.neg_mulVec, Matrix.mulVec_smul, toReal_neg, toReal_half, toReal_neg]
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    have hab := abs_le.mp (heq i)
    have hmul : w * (toReal (P.be i) - |toReal (P.be_error i)|) ≤ w * (toRealMat P.Ae *ᵥ y) i :=
      mul_le_mul_of_nonneg_left (by linarith [hab.1]) hw0
    have hs : w * |toReal (P.be_error i)| ≤ |toReal (P.be_error i)| :=
      mul_le_of_le_one_left (abs_nonneg _) hw1
    have hkey : w * toReal (P.be i) + -(toReal (P.be i) / 2) * t = toReal (P.be i) / 2 := by
      rw [← hw]; ring
    linarith [mul_sub w (toReal (P.be i)) |toReal (P.be_error i)|]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
