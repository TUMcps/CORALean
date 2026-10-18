module

public import CORALean.ContSet.Interval.Float.Operations.Partition
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Real.Theorems.PartitionExact

@[expose] public section

/-!
# Each real piece of `Interval.partition` is inside the float piece

The real piece of the box's reading sits inside the float piece of the same index. The ratio
`k / splits` is bracketed without dividing by a rounded-down count: `divDown` by a count rounded
up bounds it below, and the upper bound is `1` less the lower bound of the complement.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A numerator rounded down over a count rounded up is below the ratio. -/
theorem Interval.aux_ratioLo_le (k s : ℕ) (hs : 0 < s) :
    toReal (divDown (nsmulDown k (one : 𝕋)) (nsmulUp s (one : 𝕋))) ≤
      (k : ℝ) / s := by -- --- PROOF ---
  -- the denominator is at least `s`, the numerator at most `k`
  have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hy : (s : ℝ) ≤ toReal (nsmulUp s (one : 𝕋)) := by
    have := le_nsmulUp s (one : 𝕋)
    rwa [toReal_one, mul_one] at this
  have hypos : 0 < toReal (nsmulUp s (one : 𝕋)) := lt_of_lt_of_le hs' hy
  have hk : toReal (nsmulDown k (one : 𝕋)) ≤ k := by
    have := nsmulDown_le k (one : 𝕋)
    rwa [toReal_one, mul_one] at this
  calc toReal (divDown (nsmulDown k (one : 𝕋)) (nsmulUp s (one : 𝕋)))
      ≤ toReal (nsmulDown k (one : 𝕋)) / toReal (nsmulUp s (one : 𝕋)) :=
        divDown_le_div _ _ hypos
    _ ≤ (k : ℝ) / toReal (nsmulUp s (one : 𝕋)) := by gcongr
    _ ≤ (k : ℝ) / s := by gcongr

/-- The ratio is below `1` less the lower bound of its complement. -/
theorem Interval.aux_le_ratioHi (k s : ℕ) (hs : 0 < s) (hk : k ≤ s) :
    (k : ℝ) / s ≤ toReal (subUp (one : 𝕋)
      (divDown (nsmulDown (s - k) (one : 𝕋)) (nsmulUp s (one : 𝕋)))) := by -- --- PROOF ---
  have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have h1 := Interval.aux_ratioLo_le (𝕋 := 𝕋) (s - k) s hs
  have h2 := sub_le_subUp (one : 𝕋)
    (divDown (nsmulDown (s - k) (one : 𝕋)) (nsmulUp s (one : 𝕋)))
  rw [toReal_one] at h2
  have h3 : ((s - k : ℕ) : ℝ) / s = 1 - (k : ℝ) / s := by
    rw [Nat.cast_sub hk]; field_simp
  linarith

/-- One coordinate: the real piece `[a + k d, a + (k + 1) d]`, `d = (b - a) / s`, is inside the
float one. -/
theorem Interval.aux_partition_piece (a b : 𝕋) (s k : ℕ) (hs : 0 < s) (hk : k < s) : -- --- STMT ---
    toReal (addDown a (Interval.mulLo
        (divDown (nsmulDown k (one : 𝕋)) (nsmulUp s (one : 𝕋)))
        (subUp one (divDown (nsmulDown (s - k) (one : 𝕋)) (nsmulUp s (one : 𝕋))))
        (subDown b a) (subUp b a)))
      ≤ toReal a + (k : ℝ) * ((toReal b - toReal a) / s) ∧
    toReal a + ((k : ℝ) + 1) * ((toReal b - toReal a) / s) ≤
      toReal (addUp a (Interval.mulHi
        (divDown (nsmulDown (k + 1) (one : 𝕋)) (nsmulUp s (one : 𝕋)))
        (subUp one (divDown (nsmulDown (s - (k + 1)) (one : 𝕋)) (nsmulUp s (one : 𝕋))))
        (subDown b a) (subUp b a))) := by -- --- PROOF ---
  have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  -- the width is bracketed by the rounded differences
  have hw₁ : toReal (subDown b a) ≤ toReal b - toReal a := subDown_le_sub b a
  have hw₂ : toReal b - toReal a ≤ toReal (subUp b a) := sub_le_subUp b a
  -- the ratio and the width are each bracketed, so their product is between the corners
  have hlo := Interval.mul_between_corners
    (Interval.aux_ratioLo_le (𝕋 := 𝕋) k s hs)
    (Interval.aux_le_ratioHi (𝕋 := 𝕋) k s hs hk.le) hw₁ hw₂
  have hhi := Interval.mul_between_corners
    (Interval.aux_ratioLo_le (𝕋 := 𝕋) (k + 1) s hs)
    (Interval.aux_le_ratioHi (𝕋 := 𝕋) (k + 1) s hs hk) hw₁ hw₂
  -- the real piece is the same product written with `(b - a) / s`
  have e1 : (k : ℝ) / s * (toReal b - toReal a) = (k : ℝ) * ((toReal b - toReal a) / s) := by
    ring
  have e2 : (((k + 1 : ℕ) : ℝ)) / s * (toReal b - toReal a) =
      ((k : ℝ) + 1) * ((toReal b - toReal a) / s) := by
    push_cast; ring
  rw [e1] at hlo
  rw [e2] at hhi
  -- one rounding more at each end
  have h1 := addDown_le_add a (Interval.mulLo
        (divDown (nsmulDown k (one : 𝕋)) (nsmulUp s (one : 𝕋)))
        (subUp one (divDown (nsmulDown (s - k) (one : 𝕋)) (nsmulUp s (one : 𝕋))))
        (subDown b a) (subUp b a))
  have h2 := add_le_addUp a (Interval.mulHi
        (divDown (nsmulDown (k + 1) (one : 𝕋)) (nsmulUp s (one : 𝕋)))
        (subUp one (divDown (nsmulDown (s - (k + 1)) (one : 𝕋)) (nsmulUp s (one : 𝕋))))
        (subDown b a) (subUp b a))
  constructor <;> linarith [hlo.1, hhi.2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Each real piece is inside the float piece with the same index. -/
theorem Interval.partition_piece (I : Interval (Vec 𝕋 n)) (splits : ℕ)
    (ind : Fin n → Fin splits) :
    (I.nominal.partition splits ind).construct ⊆
      (I.partition splits ind).construct := by -- --- PROOF ---
  -- coordinate by coordinate, the piece of the one index
  intro x hx i
  have hs : 0 < splits := lt_of_le_of_lt (Nat.zero_le _) (ind i).isLt
  have h := hx i
  have hp := Interval.aux_partition_piece (I.inf i) (I.sup i) splits (ind i) hs (ind i).isLt
  exact ⟨le_trans hp.1 h.1, le_trans h.2 hp.2⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
