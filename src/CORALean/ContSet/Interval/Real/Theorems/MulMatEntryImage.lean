module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Definitions.Coefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The product of an interval matrix and a real matrix, entry by entry

[1, Prop. 5]: for an interval matrix `[M]` and a real matrix `N`, the product `[M] N` has center
`mid[M] N` and radius `rad[M] |N|`. Read as the interval hull of `{M N | M ∈ [M]}`, entry by
entry, and proved exact: entry `(i, j)` of `M N` ranges over exactly
`[(mid[M] N)ᵢⱼ - (rad[M] |N|)ᵢⱼ, (mid[M] N)ᵢⱼ + (rad[M] |N|)ᵢⱼ]` as `M` ranges over `[M]`. The
upper end is reached by moving row `i` of `M` to whichever end of its interval agrees in sign with
column `j` of `N`, and every value between by moving it part of the way. `[M]` must be nonempty,
every `inf ≤ sup`, as an interval matrix of the paper is.

## Inputs
* `IM` – interval matrix
* `N` – real matrix
* `i` – row index
* `j` – column index

## Hypotheses
* `hIM` – `IM` has ordered bounds

## Conclusion
* entry `(i, j)` of the product ranges exactly over the center-radius interval

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.image_mul_apply_eq (IM : Interval (Mat ℝ n p))
    (hIM : ∀ i k, IM.inf i k ≤ IM.sup i k) (N : Mat ℝ p q) (i : Fin n)
    (j : Fin q) : -- --- CONCL ---
    (fun M : Mat ℝ n p => (M * N) i j) '' IM.construct =
      Set.Icc ((IM.center * N) i j - (IM.radius * N.map abs) i j)
        ((IM.center * N) i j + (IM.radius * N.map abs) i j) := by -- --- PROOF ---
  have hc : ∀ a k, IM.center a k = (IM.inf a k + IM.sup a k) / 2 := fun a k => by
    simp only [Interval.center, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]; ring
  have hr : ∀ a k, IM.radius a k = (IM.sup a k - IM.inf a k) / 2 := fun a k => by
    simp only [Interval.radius, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]; ring
  have hmem : ∀ M : Mat ℝ n p, M ∈ IM.construct ↔ ∀ a k, IM.inf a k ≤ M a k ∧ M a k ≤ IM.sup a k :=
    fun M => ⟨fun h a k => h (a, k), fun h ak => h ak.1 ak.2⟩
  -- the spread of the entry about the center's
  have hdev : ∀ M : Mat ℝ n p, (M * N) i j - (IM.center * N) i j
      = ∑ k, (M i k - IM.center i k) * N k j := fun M => by
    simp only [Matrix.mul_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  set r := (IM.radius * N.map abs) i j with hrdef
  have hrsum : r = ∑ k, IM.radius i k * |N k j| := by simp [hrdef, Matrix.mul_apply]
  ext v
  constructor
  · -- every product lands in the interval
    rintro ⟨M, hM, rfl⟩
    rw [hmem] at hM
    have hb : |(M * N) i j - (IM.center * N) i j| ≤ r := by
      rw [hdev, hrsum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [abs_le, hc, hr]
      constructor <;> linarith [(hM i k).1, (hM i k).2]
    rw [abs_le] at hb
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  · -- every value of the interval is reached by moving row `i` part of the way
    rintro ⟨hlo, hhi⟩
    have hrnn : 0 ≤ r := by linarith
    have hvr : |v - (IM.center * N) i j| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    set t := Zonotope.coefficient r (v - (IM.center * N) i j)
    have ht : |t| ≤ 1 := Zonotope.abs_coefficient_le_one hrnn hvr
    let s : Fin p → ℝ := fun k => if 0 ≤ N k j then 1 else -1
    have hs : ∀ k, s k * N k j = |N k j| := fun k => by
      by_cases h : 0 ≤ N k j
      · simp [s, h, abs_of_nonneg h]
      · simp [s, h, abs_of_neg (not_le.mp h)]
    have hs1 : ∀ k, |s k| = 1 := fun k => by by_cases h : 0 ≤ N k j <;> simp [s, h]
    -- row `i` moved by the fraction `t` of its radius, towards the sign of column `j`
    let M : Mat ℝ n p := fun a k =>
      if a = i then IM.center a k + t * s k * IM.radius a k else IM.center a k
    refine ⟨M, (hmem M).mpr fun a k => ?_, ?_⟩
    · have hrk : 0 ≤ IM.radius a k := by rw [hr]; linarith [hIM a k]
      have hts : |t * s k| ≤ 1 := by rw [abs_mul, hs1, mul_one]; exact ht
      have hle : |t * s k * IM.radius a k| ≤ IM.radius a k := by
        rw [abs_mul, abs_of_nonneg hrk]
        exact mul_le_of_le_one_left hrk hts
      rw [abs_le] at hle
      by_cases ha : a = i
      · subst ha
        simp only [M, if_true]
        rw [hc, hr] at *
        constructor <;> linarith [hle.1, hle.2]
      · simp only [M, ha, if_false]
        rw [hc]
        constructor <;> linarith [hIM a k]
    · -- the moved entry is the center's plus `t r`, which is `v`
      have hdM := hdev M
      have hsum : ∑ k, (M i k - IM.center i k) * N k j = t * r := by
        rw [hrsum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [M, if_true]
        rw [← hs k]; ring
      have htr : r * t = v - (IM.center * N) i j := Zonotope.mul_coefficient hvr
      show (M * N) i j = v
      linarith [hdM, hsum, htr]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
