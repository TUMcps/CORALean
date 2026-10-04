import CORALean.ContSet.SpectraShadow.Float.Operations.Inter
import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero
import CORALean.ContSet.SpectraShadow.Real.Theorems.LmiAppend

/-!
# `SpectraShadow.inter` over-approximates the intersection

A point of both sets is `y₁ + e₁ = y₂ + e₂` with `yₖ` nominal at the variables `βₖ` and `eₖ` in
its box. The witness is `y₁` at `[β₁; β₂]` with `e₁`: the first block of the inequality is the
two inequalities side by side, which hold, and the diagonal block reads `lo + (y₁ - c₁) -
(y₂ - c₂)` and `hi - (y₁ - c₁) + (y₂ - c₂)`, nonnegative because `y₁ - y₂ = e₂ - e₁` lies between
the bounds `lo` and `hi` were rounded outward from.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum of block-diagonal terms is the block-diagonal of the two sums. -/
theorem SpectraShadow.aux_lmi_blockDiag {a b m : ℕ} (X₀ : Mat ℝ a a) (Y₀ : Mat ℝ b b)
    (X : Fin m → Mat ℝ a a) (Y : Fin m → Mat ℝ b b) (β : Fin m → ℝ) :
    blockDiag 0 X₀ Y₀ + ∑ i, β i • blockDiag 0 (X i) (Y i)
      = blockDiag 0 (X₀ + ∑ i, β i • X i) (Y₀ + ∑ i, β i • Y i) := by
  simp_rw [← blockDiag_smul]
  rw [← blockDiag_sum, ← blockDiag_add]

/-- A float diagonal, read as reals, is the diagonal of the vector read as reals. -/
theorem SpectraShadow.aux_toRealMat_diagonalBlock (v : Vec 𝕋 n) :
    toRealMat (diagonalBlock v) = diagonal (toRealVec v) :=
  funext fun i => funext fun l => toReal_diagonalBlock v i l

/-- A weighted sum of diagonals is the diagonal of the weighted sum. -/
theorem SpectraShadow.aux_diagonal_sum {m : ℕ} (d₀ : Vec ℝ n) (d : Fin m → Vec ℝ n)
    (β : Fin m → ℝ) :
    diagonal d₀ + ∑ i, β i • diagonal (d i)
      = diagonal fun r => d₀ r + ∑ i, β i * d i r := by -- --- PROOF ---
  ext j k
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  split_ifs with h
  · subst h; rfl
  · simp

/-- The plus block holds when both inequalities do. -/
theorem SpectraShadow.aux_posSemidef_plus_of (S₁ S₂ : SpectraShadow 𝕋 n)
    (β₁ : Fin S₁.m → ℝ) (β₂ : Fin S₂.m → ℝ)
    (h₁ : (toRealMat S₁.A₀ + ∑ i, β₁ i • toRealMat (S₁.A i)).PosSemidef)
    (h₂ : (toRealMat S₂.A₀ + ∑ j, β₂ j • toRealMat (S₂.A j)).PosSemidef) :
    (toRealMat (S₁.plus S₂).A₀ + ∑ i : Fin (S₁.plus S₂).m,
      Fin.append β₁ β₂ i • toRealMat ((S₁.plus S₂).A i)).PosSemidef := by -- --- PROOF ---
  have hA : ∀ i : Fin (S₁.m + S₂.m), toRealMat ((S₁.plus S₂).A i)
      = (Fin.append (fun i => blockDiag 0 (toRealMat (S₁.A i)) 0)
          (fun j => blockDiag 0 0 (toRealMat (S₂.A j)))
          : Fin (S₁.m + S₂.m) → Mat ℝ (S₁.k + S₂.k) (S₁.k + S₂.k)) i := by
    intro i
    refine Fin.addCases (fun p => ?_) (fun p => ?_) i
    · simp only [SpectraShadow.plus, Fin.append_left, SpectraShadow.toRealMat_blockDiag,
        SpectraShadow.toRealMat_const_zero]
    · simp only [SpectraShadow.plus, Fin.append_right, SpectraShadow.toRealMat_blockDiag,
        SpectraShadow.toRealMat_const_zero]
  have h₀ : toRealMat (S₁.plus S₂).A₀ = blockDiag 0 (toRealMat S₁.A₀) (toRealMat S₂.A₀) :=
    SpectraShadow.toRealMat_blockDiag _ _
  -- the two inequalities, side by side
  have e : toRealMat (S₁.plus S₂).A₀ + ∑ i : Fin (S₁.plus S₂).m,
        Fin.append β₁ β₂ i • toRealMat ((S₁.plus S₂).A i)
      = blockDiag 0 (toRealMat S₁.A₀ + ∑ i, β₁ i • toRealMat (S₁.A i))
          (toRealMat S₂.A₀ + ∑ j, β₂ j • toRealMat (S₂.A j)) := by
    rw [h₀, Finset.sum_congr rfl fun i _ => by rw [hA i]]
    have := Real.SpectraShadow.lmi_append (toRealMat S₁.A₀) (toRealMat S₂.A₀)
      (fun i => toRealMat (S₁.A i)) (fun j => toRealMat (S₂.A j)) (Fin.append β₁ β₂)
    simp only [Fin.append_left, Fin.append_right] at this
    exact this
  rw [e]
  exact (posSemidef_blockDiag_iff _ _).mpr ⟨h₁, h₂⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.inter_outer (S₁ S₂ : SpectraShadow 𝕋 n) :
    S₁.construct ∩ S₂.construct ⊆ (S₁.inter S₂).construct := by -- --- PROOF ---
  rintro x ⟨⟨y₁, hy₁', e₁, he₁, hx₁⟩, y₂, hy₂', e₂, he₂, hx₂⟩
  obtain ⟨β₁, hP₁, hy₁⟩ := SpectraShadow.mem_nominalSet_iff.mp hy₁'
  obtain ⟨β₂, hP₂, hy₂⟩ := SpectraShadow.mem_nominalSet_iff.mp hy₂'
  have hxr : ∀ r, y₁ r - y₂ r = e₂ r - e₁ r := fun r => by
    have h1 : y₁ r + e₁ r = x r := congrFun hx₁ r
    have h2 : y₂ r + e₂ r = x r := congrFun hx₂ r
    linarith
  -- the difference generators against `[β₁; β₂]` give the difference of the two nominal points
  have hg : ∀ r, ∑ i, Fin.append β₁ β₂ i
        * toReal (Fin.append (S₁.G r) (fun j => neg (S₂.G r j)) i)
      = (y₁ r - toReal (S₁.c r)) - (y₂ r - toReal (S₂.c r)) := by
    intro r
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, toReal_neg, mul_neg, Finset.sum_neg_distrib]
    rw [hy₁ r, hy₂ r]
    have e₁' : ∑ j, β₁ j * toReal (S₁.G r j) = ∑ j, toReal (S₁.G r j) * β₁ j :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have e₂' : ∑ j, β₂ j * toReal (S₂.G r j) = ∑ j, toReal (S₂.G r j) * β₂ j :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [e₁', e₂']
    ring
  refine ⟨y₁, SpectraShadow.mem_nominalSet_iff.mpr ⟨Fin.append β₁ β₂, ?_, fun r => ?_⟩,
    e₁, he₁, hx₁⟩
  · -- the inequality: the plus block, then the two diagonals
    show (toRealMat (blockDiag (FloatOps.zero : 𝕋) (S₁.plus S₂).A₀
        (blockDiag (FloatOps.zero : 𝕋) (diagonalBlock _) (diagonalBlock _)))
      + ∑ i, Fin.append β₁ β₂ i • toRealMat (blockDiag (FloatOps.zero : 𝕋) ((S₁.plus S₂).A i)
        (blockDiag (FloatOps.zero : 𝕋) (diagonalBlock _) (diagonalBlock _)))).PosSemidef
    simp only [SpectraShadow.toRealMat_blockDiag, SpectraShadow.aux_toRealMat_diagonalBlock]
    rw [SpectraShadow.aux_lmi_blockDiag, SpectraShadow.aux_lmi_blockDiag,
      SpectraShadow.aux_diagonal_sum, SpectraShadow.aux_diagonal_sum]
    refine (posSemidef_blockDiag_iff _ _).mpr ⟨SpectraShadow.aux_posSemidef_plus_of S₁ S₂ β₁ β₂
      hP₁ hP₂, (posSemidef_blockDiag_iff _ _).mpr ⟨posSemidef_diagonal_iff.mpr fun r => ?_,
        posSemidef_diagonal_iff.mpr fun r => ?_⟩⟩
    · -- `lo + (y₁ - y₂) - (c₁ - c₂) ≥ 0`: `lo` covers `c₁ - c₂ - (e₂ - e₁)`
      have h := hg r
      have hb₁ : toReal (S₁.E.inf r) ≤ e₁ r ∧ e₁ r ≤ toReal (S₁.E.sup r) := he₁ r
      have hb₂ : toReal (S₂.E.inf r) ≤ e₂ r ∧ e₂ r ≤ toReal (S₂.E.sup r) := he₂ r
      have r1 := sub_le_subUp (S₁.c r) (S₂.c r)
      have r2 := sub_le_subUp (S₁.E.sup r) (S₂.E.inf r)
      have r3 := add_le_addUp (subUp (S₁.c r) (S₂.c r)) (subUp (S₁.E.sup r) (S₂.E.inf r))
      simp only [toRealVec] at h ⊢
      linarith [hxr r]
    · -- `hi - (y₁ - y₂) + (c₁ - c₂) ≥ 0`: `hi` covers `c₂ - c₁ + (e₂ - e₁)`
      have h := hg r
      have hb₁ : toReal (S₁.E.inf r) ≤ e₁ r ∧ e₁ r ≤ toReal (S₁.E.sup r) := he₁ r
      have hb₂ : toReal (S₂.E.inf r) ≤ e₂ r ∧ e₂ r ≤ toReal (S₂.E.sup r) := he₂ r
      have r1 := sub_le_subUp (S₂.c r) (S₁.c r)
      have r2 := sub_le_subUp (S₂.E.sup r) (S₁.E.inf r)
      have r3 := add_le_addUp (subUp (S₂.c r) (S₁.c r)) (subUp (S₂.E.sup r) (S₁.E.inf r))
      simp only [toRealVec, toReal_neg, mul_neg, Finset.sum_neg_distrib] at h ⊢
      linarith [hxr r]
  · -- the point is the first set's, the second block of generators being zero
    rw [hy₁ r]
    show _ = toReal (S₁.c r) + ∑ j : Fin (S₁.m + S₂.m),
      toReal (Fin.append (S₁.G r) (fun _ => (zero : 𝕋)) j) * Fin.append β₁ β₂ j
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, toReal_zero, zero_mul,
      Finset.sum_const_zero, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
