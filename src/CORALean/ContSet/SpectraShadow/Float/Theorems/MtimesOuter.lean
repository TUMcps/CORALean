module

public import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.SpectraShadow.Float.Operations.Mtimes
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero

@[expose] public section

/-!
# `SpectraShadow.mtimes` contains the image

Multiplying by a matrix rounds nothing in the nominal shadow, so `InflatedContSet.image_subset`
splits this into the nominal shadow and the box. A point `x = c + Gβ` of the nominal shadow is
carried to the point `M x` of the result at the variables `(β, x)`: the equalities hold, so
their diagonal block is zero and the whole inequality is the old one beside it. The box is
`Interval.mtimes_outer`.

## Inputs
* `M` – `m × n` matrix
* `S` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* `SpectraShadow.mtimes` contains the image
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open scoped Matrix
open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] in
/-- Over ℝ and with plain dimensions: the inequality is the old one beside a zero block as soon as
the equalities' diagonal vanishes. -/
theorem SpectraShadow.aux_lmi_block {k a b : ℕ} (A₀ : Mat ℝ k k) (A : Fin a → Mat ℝ k k)
    (d₀ : Vec ℝ (n + n)) (dβ : Fin a → Vec ℝ (n + n)) (dz : Fin b → Vec ℝ (n + n))
    (β : Fin a → ℝ) (z : Fin b → ℝ)
    (hD : d₀ + ∑ j, β j • dβ j + ∑ i, z i • dz i = 0) : -- --- CONCL ---
    blockDiag 0 A₀ (Matrix.diagonal d₀)
      + (∑ j, β j • blockDiag 0 (A j) (Matrix.diagonal (dβ j))
        + ∑ i, z i • blockDiag 0 (0 : Mat ℝ k k) (Matrix.diagonal (dz i)))
      = blockDiag 0 (A₀ + ∑ j, β j • A j) 0 := by -- --- PROOF ---
  simp only [← blockDiag_smul, ← blockDiag_sum, ← blockDiag_add]
  congr 1
  · simp
  · ext r r'
    have h := congrFun hD r
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply,
      Matrix.zero_apply, smul_eq_mul]
    by_cases hrr : r = r'
    · subst hrr
      simpa [add_assoc] using h
    · simp [hrr]

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `mtimes`'s variable count, stated through the projection because
that is the form the goal has. -/
theorem SpectraShadow.aux_sum_mtimes (M : Mat 𝕋 m n) (S : SpectraShadow 𝕋 (Vec 𝕋 n))
    {R : Type} [AddCommMonoid R] (f : Fin (S.mtimes M).m → R) :
    ∑ l : Fin (S.mtimes M).m, f l = ∑ j, f (Fin.castAdd n j) + ∑ i, f (Fin.natAdd S.m i) :=
  Fin.sum_univ_add (a := S.m) (b := n) f

/-- At the variables `(β, z)` with `z` the shadow's own point, the stored inequality is the old
one beside a zero block. -/
theorem SpectraShadow.aux_mtimes_lmi (M : Mat 𝕋 m n) (S : SpectraShadow 𝕋 (Vec 𝕋 n))
    (v : Fin (S.mtimes M).m → ℝ) (z : Vec ℝ n)
    (hz : ∀ i, z i = toReal (S.c i) + ∑ j, toReal (S.G j i) * v (Fin.castAdd n j))
    (hv : ∀ i, v (Fin.natAdd S.m i) = z i) : -- --- CONCL ---
    toRealMat (S.mtimes M).A₀ + ∑ l, v l • toRealMat ((S.mtimes M).A l)
      = blockDiag 0 (toRealMat S.A₀ + ∑ j, v (Fin.castAdd n j) • toRealMat (S.A j))
        0 := by -- --- PROOF ---
  -- the stored diagonal blocks, read as reals
  have hd : ∀ w : Vec 𝕋 (n + n), toRealMat (diagonalBlock w) = Matrix.diagonal (toRealVec w) := by
    intro w
    ext i l
    simp [toRealMat, toReal_diagonalBlock]
  -- the two variable blocks split, and every stored matrix is read as the real one
  rw [SpectraShadow.aux_sum_mtimes]
  simp only [SpectraShadow.mtimes, Fin.append_left, Fin.append_right,
    SpectraShadow.toRealMat_blockDiag, SpectraShadow.toRealMat_const_zero, hd]
  -- the old inequality beside the diagonal block of the equalities
  refine SpectraShadow.aux_lmi_block (toRealMat S.A₀) (fun j => toRealMat (S.A j))
    (toRealVec (Fin.append (-S.c) S.c))
    (fun j => toRealVec (Fin.append (-(S.G j)) fun i => S.G j i))
    (fun i => toRealVec (Fin.append (fun r => if r = i then one else zero)
      fun r => if r = i then neg one else zero))
    (fun j => v (Fin.castAdd n j)) (fun i => v (Fin.natAdd S.m i)) ?_
  -- the equalities' diagonal entries are the point minus its definition, and its negation
  funext r
  have hite : ∀ (P : Prop) [Decidable P],
      toReal (if P then (one : 𝕋) else zero) = if P then 1 else 0 :=
    fun P _ => by split_ifs <;> simp [toReal_one, toReal_zero]
  have hite' : ∀ (P : Prop) [Decidable P],
      toReal (if P then neg (one : 𝕋) else zero) = if P then -1 else 0 :=
    fun P _ => by split_ifs <;> simp [toReal_neg, toReal_one, toReal_zero]
  -- first the entry for `z - c - Gβ ≥ 0`, then the one for its negation
  refine Fin.addCases (fun i => ?_) (fun i => ?_) r
  · have h := hz i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      toRealVec, Fin.append_left, hv, Pi.neg_apply, toReal_neg', hite, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_neg]
    have h2 : ∑ x, v (Fin.castAdd n x) * toReal (S.G x i)
        = ∑ x, toReal (S.G x i) * v (Fin.castAdd n x) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [Finset.sum_neg_distrib, h2]
    linarith
  · have h := hz i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      toRealVec, Fin.append_right, hv, hite', mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_neg]
    have h2 : ∑ x, v (Fin.castAdd n x) * toReal (S.G x i)
        = ∑ x, toReal (S.G x i) * v (Fin.castAdd n x) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [h2]
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.mtimes_outer (M : Mat 𝕋 m n) (S : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' S.construct ⊆ (S.mtimes M).construct :=
  image_subset (fun x y => Matrix.mulVec_add _ x y)
    (by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨β, hP, hxβ⟩ := SpectraShadow.mem_nominalSet_iff.mp hx
      -- the new variables are the old ones and the point itself
      refine SpectraShadow.mem_nominalSet_iff.mpr
        ⟨Fin.append β x, ?_, fun r => ?_⟩
      · have e := SpectraShadow.aux_mtimes_lmi M S (Fin.append β x) x
          (fun i => by simpa using hxβ i) (fun i => by simp)
        have hβ : ∀ j, (Fin.append β x : Fin (S.m + n) → ℝ) (Fin.castAdd n j) = β j :=
          fun j => Fin.append_left _ _ j
        simp only [hβ] at e
        rw [e]
        exact (posSemidef_blockDiag_iff _ _).mpr ⟨hP, Matrix.PosSemidef.zero⟩
      · -- the generators `[0 | M]` pick the second block of variables, which holds the point
        show (toRealMat M *ᵥ x) r = toReal (zero : 𝕋)
          + ∑ l : Fin (S.m + n), toReal (Fin.append (fun _ : Fin S.m => (zero : 𝕋))
              (fun i => M r i) l) * (Fin.append β x : Fin (S.m + n) → ℝ) l
        rw [Fin.sum_univ_add]
        simp [toReal_zero, Matrix.mulVec, dotProduct, toRealMat])
    (Interval.mtimes_outer M S.I_error)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
