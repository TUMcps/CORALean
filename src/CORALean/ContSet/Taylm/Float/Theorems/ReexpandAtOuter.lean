module

public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Taylm.Float.Operations.ReexpandAt
public import CORALean.ContSet.Taylm.Float.Theorems.AbsPolyOfRoundLe
public import CORALean.ContSet.Taylm.Float.Theorems.BinomCoefMem
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfAppend
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# `Taylm.reexpandAt` encloses the function with one variable substituted

The new polynomial at `s` is the original at `s` with `sₖ` replaced by `m + r sₖ`
(`aux_polyOf_reexpPairs`), up to the width of the stored coefficients' brackets
(`abs_polyOf_round_le`), which the error box takes in; and for `|m| + |r| ≤ 1` that point is again
in the normalized box, where the original remainder and box hold.

## Inputs
* `T` – Taylor model
* `g` – enclosed function
* `k` – variable index
* `m` – center
* `r` – radius

## Hypotheses
* `h` – the model encloses the function
* `hmr` – center plus radius stays within the unit interval

## Conclusion
* the result encloses the function with that variable substituted
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A monomial split at one variable. -/
theorem Taylm.aux_monomial_split (e : Fin n → ℕ) (t : Vec ℝ n) (k : Fin n) :
    Real.Taylm.monomial e t = t k ^ e k * ∏ i ∈ Finset.univ.erase k, t i ^ e i :=
  (Finset.mul_prod_erase Finset.univ (fun i => t i ^ e i) (Finset.mem_univ k)).symm


/-- One term, expanded: the binomial theorem in the exponent of the variable. -/
theorem Taylm.aux_term_expand (a : ℝ) (e : Fin n → ℕ) (s : Vec ℝ n) (k : Fin n)
    (m r : ℝ) : -- --- CONCL ---
    a * Real.Taylm.monomial e (Function.update s k (m + r * s k)) =
      ∑ j ∈ Finset.range (e k + 1),
        (a * ((e k).choose j * m ^ (e k - j) * r ^ j)) *
          Real.Taylm.monomial (Function.update e k j) s := by -- --- PROOF ---
  have hL : Real.Taylm.monomial e (Function.update s k (m + r * s k))
      = (m + r * s k) ^ e k * ∏ i ∈ Finset.univ.erase k, s i ^ e i := by
    rw [Taylm.aux_monomial_split e _ k, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hR : ∀ j, Real.Taylm.monomial (Function.update e k j) s
      = s k ^ j * ∏ i ∈ Finset.univ.erase k, s i ^ e i := fun j => by
    rw [Taylm.aux_monomial_split _ s k, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hb : (m + r * s k) ^ e k = ∑ j ∈ Finset.range (e k + 1),
      ((e k).choose j : ℝ) * m ^ (e k - j) * r ^ j * s k ^ j := by
    rw [add_comm, add_pow]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_pow]; ring
  rw [hL, hb, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hR]; ring


/-- One variable's re-expansion is exact. -/
theorem Taylm.aux_polyOf_reexpPairs (L : List (𝕋 × (Fin n → ℕ))) (k : Fin n) (m r : 𝕋)
    (s : Vec ℝ n) : -- --- CONCL ---
    Real.Taylm.polyOf ((L.flatMap fun a => (List.range (a.2 k + 1)).map fun j => (a, j)).map
        fun q => (toReal q.1.1 * (((q.1.2 k).choose q.2 : ℝ) * toReal m ^ (q.1.2 k - q.2)
          * toReal r ^ q.2), Function.update q.1.2 k q.2)) s =
      Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2))
        (Function.update s k (toReal m + toReal r * s k)) := by -- --- PROOF ---
  induction L with
  | nil => simp [Real.Taylm.polyOf]
  | cons a L ih =>
    rw [List.flatMap_cons, List.map_append, Real.Taylm.polyOf_append, ih, List.map_cons,
      Real.Taylm.polyOf_cons]
    congr 1
    simp only [Real.Taylm.polyOf, List.map_map, Function.comp_def]
    rw [Taylm.aux_term_expand]
    rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.reexpandAt_outer {T : Taylm 𝕋 n} {g : Vec ℝ n → ℝ} (h : T.Encloses g) (k : Fin n)
    (m r : 𝕋) (hmr : |toReal m| + |toReal r| ≤ 1) : -- --- CONCL ---
    (T.reexpandAt k m r).Encloses
      fun s => g (Function.update s k (toReal m + toReal r * s k)) := by -- --- PROOF ---
  intro s hs
  -- the substituted point is in the normalized box
  have hp : Function.update s k (toReal m + toReal r * s k) ∈ Real.Taylm.box n := by
    intro i
    by_cases hi : i = k
    · subst hi
      rw [Function.update_self]
      calc |toReal m + toReal r * s i| ≤ |toReal m| + |toReal r * s i| := abs_add_le _ _
        _ = |toReal m| + |toReal r| * |s i| := by rw [abs_mul]
        _ ≤ |toReal m| + |toReal r| * 1 :=
          add_le_add_right (mul_le_mul_of_nonneg_left (hs i) (abs_nonneg _)) _
        _ ≤ 1 := by linarith
    · rw [Function.update_of_ne hi]
      exact hs i
  have hr := h _ hp
  -- the exact expansion against the stored upper corners
  have hround := Taylm.abs_polyOf_round_le (T.aux_reexpPairs k)
    (fun p => (Taylm.aux_reexpCoef k m r p).inf) (fun p => (Taylm.aux_reexpCoef k m r p).sup)
    (fun q => toReal q.1.1 * (((q.1.2 k).choose q.2 : ℝ) * toReal m ^ (q.1.2 k - q.2)
      * toReal r ^ q.2)) (fun q => Function.update q.1.2 k q.2)
    (fun q _ => Interval.mul_between_corners (le_refl _) (le_refl _)
      (Taylm.binomCoef_mem (q.1.2 k) q.2 m r).1 (Taylm.binomCoef_mem (q.1.2 k) q.2 m r).2) hs
  -- the exact expansion is the original polynomial at the substituted point
  have hex : Real.Taylm.polyOf ((T.aux_reexpPairs k).map fun q => (toReal q.1.1 *
        (((q.1.2 k).choose q.2 : ℝ) * toReal m ^ (q.1.2 k - q.2) * toReal r ^ q.2),
        Function.update q.1.2 k q.2)) s =
      Real.Taylm.polyOf (T.terms.map fun a => (toReal a.1, a.2))
        (Function.update s k (toReal m + toReal r * s k)) :=
    Taylm.aux_polyOf_reexpPairs T.terms k m r s
  -- the box's two ends, rounded outward by the stored coefficients' width
  have hlo := subDown_le_sub T.I_error.inf (listSumUp ((T.aux_reexpPairs k).map fun p =>
    subUp (Taylm.aux_reexpCoef k m r p).sup (Taylm.aux_reexpCoef k m r p).inf))
  have hhi := add_le_addUp T.I_error.sup (listSumUp ((T.aux_reexpPairs k).map fun p =>
    subUp (Taylm.aux_reexpCoef k m r p).sup (Taylm.aux_reexpCoef k m r p).inf))
  simp only [Taylm.inflated, Real.Taylm.poly] at hr ⊢
  -- the stored polynomial, spelt as a sum over the pairs
  have hrw : Real.Taylm.polyOf ((T.reexpandAt k m r).terms.map fun a => (toReal a.1, a.2)) s
      = Real.Taylm.polyOf
        ((T.aux_reexpPairs k).map fun p => (toReal (Taylm.aux_reexpCoef k m r p).sup,
        Function.update p.1.2 k p.2)) s := by
    simp only [Taylm.reexpandAt, List.map_map, Function.comp_def]
  rw [hrw]
  have habs := abs_le.1 hround
  rw [hex] at habs
  simp only [Taylm.reexpandAt]
  constructor <;> linarith [hr.1, hr.2, habs.1, habs.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
