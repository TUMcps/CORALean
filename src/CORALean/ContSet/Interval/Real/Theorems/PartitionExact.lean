import CORALean.ContSet.Interval.Real.Operations.Partition
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# `Interval.partition` covers the box it cuts

The `splits ^ n` sub-boxes have the box as their union, a cover and not a partition: neighbouring
pieces share their common face. Each sub-box lies inside `I`, and a point of `I` falls in the piece
of every coordinate whose range holds it, found by the floor of its relative position.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One coordinate: a point of `[a, b]` lies in one of the `s` equal pieces. -/
theorem Interval.aux_partition_exists (a b x : ℝ) (s : ℕ) (hs : 0 < s) (h1 : a ≤ x)
    (h2 : x ≤ b) :
    ∃ k : Fin s, a + (k : ℝ) * ((b - a) / s) ≤ x ∧
      x ≤ a + ((k : ℝ) + 1) * ((b - a) / s) := by -- --- PROOF ---
  have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  rcases eq_or_lt_of_le (le_trans h1 h2) with hab | hab
  · subst hab
    refine ⟨⟨0, hs⟩, ?_, ?_⟩ <;> simp <;> linarith
  · have hd : 0 < (b - a) / s := div_pos (by linarith) hs'
    set d := (b - a) / s with hdd
    have hbd : b - a = s * d := by rw [hdd]; field_simp
    set u := (x - a) / d with hu
    have hu0 : 0 ≤ u := div_nonneg (by linarith) hd.le
    have hus : u ≤ s := by
      rw [hu, div_le_iff₀ hd]; nlinarith
    have hxu : x = a + u * d := by rw [hu]; field_simp; ring
    -- the piece: the integer part of `u`, capped at the last piece
    refine ⟨⟨min ⌊u⌋₊ (s - 1), lt_of_le_of_lt (min_le_right _ _) (by omega)⟩, ?_, ?_⟩
    · show a + ((min ⌊u⌋₊ (s - 1) : ℕ) : ℝ) * d ≤ x
      rw [hxu]
      have : ((min ⌊u⌋₊ (s - 1) : ℕ) : ℝ) ≤ u :=
        le_trans (Nat.cast_le.mpr (min_le_left _ _)) (Nat.floor_le hu0)
      nlinarith
    · show x ≤ a + (((min ⌊u⌋₊ (s - 1) : ℕ) : ℝ) + 1) * d
      rw [hxu]
      have : u ≤ ((min ⌊u⌋₊ (s - 1) : ℕ) : ℝ) + 1 := by
        rcases le_total ⌊u⌋₊ (s - 1) with h | h
        · rw [min_eq_left h]; exact (Nat.lt_floor_add_one u).le
        · rw [min_eq_right h]
          have : ((s - 1 : ℕ) : ℝ) + 1 = s := by
            rw [Nat.cast_sub hs]; simp
          rw [this]; exact hus
      nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.partition_exact (I : Interval (Vec ℝ n)) (splits : ℕ)
    (hs : 0 < splits) :
    (⋃ ind : Fin n → Fin splits, (I.partition splits ind).construct) =
      I.construct := by -- --- PROOF ---
  have hs' : (0 : ℝ) < splits := Nat.cast_pos.mpr hs
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨ind, hx⟩ i
    set d := (I.sup i - I.inf i) / splits with hd
    have h : I.inf i + (ind i : ℝ) * d ≤ x i ∧ x i ≤ I.inf i + ((ind i : ℝ) + 1) * d := hx i
    have hk0 : (0 : ℝ) ≤ (ind i : ℝ) := Nat.cast_nonneg _
    have hk1 : ((ind i : ℝ) + 1) ≤ splits := by exact_mod_cast (ind i).isLt
    -- the piece is nonempty, so the coordinate's range has nonnegative width
    have hw : 0 ≤ d := by linarith [h.1, h.2]
    have hwd : d * splits = I.sup i - I.inf i := by rw [hd]; field_simp
    show I.inf i ≤ x i ∧ x i ≤ I.sup i
    constructor
    · nlinarith [h.1, mul_nonneg hk0 hw]
    · nlinarith [h.2, mul_nonneg (sub_nonneg.mpr hk1) hw]
  · intro hx
    have hex := fun i => Interval.aux_partition_exists (I.inf i) (I.sup i) (x i) splits hs
      (hx i).1 (hx i).2
    choose ind hind using hex
    exact ⟨ind, fun i => hind i⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
