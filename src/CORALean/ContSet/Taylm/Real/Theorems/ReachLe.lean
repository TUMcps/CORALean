module

public import CORALean.ContSet.Taylm.Real.Operations.Reach
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.AbsPolyBoundsLe
public import CORALean.ContSet.Taylm.Real.Theorems.WeightNonneg
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# A scaled model's range is within `O(h)` of its center

What [1, Thm. 1]'s proof says of the intrinsics' remainder term: it is a power of "a bound `B` of a
function that scales at least linearly with `h`". Here that function is `f - c_f`: the constant
terms cancel against `constCoef`, every other term has degree at least one and so is at most `h`
times its weight, and the remainder is at most `C·hᴺ⁺¹ ≤ C·h`.

## Inputs
* `T` – Taylor model
* `h` – domain radius
* `C` – scaling constant

## Hypotheses
* `h0` – radius is positive
* `h1` – radius is at most one
* `hT` – the model is scaled by the constant

## Conclusion
* the range lies within a multiple of the radius of the center

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The bounds minus the constant terms are at most `h` times the weight. -/
private theorem Taylm.aux_abs_polyBounds_sub_le (L : List (ℝ × (Fin n → ℕ))) {h : ℝ} (h0 : 0 < h)
    (h1 : h ≤ 1) : -- --- CONCL ---
    |(Taylm.polyBounds L).inf - ((L.filter fun a => Taylm.degree a.2 == 0).map Prod.fst).sum|
        ≤ h * Taylm.weight L h ∧
      |(Taylm.polyBounds L).sup - ((L.filter fun a => Taylm.degree a.2 == 0).map Prod.fst).sum|
        ≤ h * Taylm.weight L h := by -- --- PROOF ---
  induction L with
  | nil => simp [Taylm.polyBounds, Taylm.weight]
  | cons a L ih =>
    simp only [Taylm.polyBounds, Taylm.weight, List.map_cons, List.sum_cons, List.filter_cons,
      mul_add] at ih ⊢
    by_cases hd : Taylm.degree a.2 = 0
    · -- a constant term is its own bound and is subtracted again
      have hta : Taylm.termBounds a = ⟨a.1, a.1⟩ := by simp [Taylm.termBounds, hd]
      simp only [hd, beq_self_eq_true, if_true, List.map_cons, List.sum_cons, hta,
        add_sub_add_left_eq_sub]
      have hw0 : 0 ≤ h * (|a.1| / h ^ 0) := by positivity
      exact ⟨by linarith [ih.1], by linarith [ih.2]⟩
    · have hb : (Taylm.degree a.2 == 0) = false := by simpa using hd
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      -- a term of positive degree is at most `h` times its weight
      have ha : |a.1| ≤ h * (|a.1| / h ^ Taylm.degree a.2) := by
        rw [mul_div_assoc', le_div_iff₀ (pow_pos h0 _)]
        have : h ^ Taylm.degree a.2 ≤ h := pow_le_of_le_one h0.le h1 hd
        nlinarith [abs_nonneg a.1]
      have ht := (Taylm.abs_polyBounds_le [a])
      simp only [Taylm.polyBounds, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero] at ht
      constructor
      · rw [add_sub_assoc]
        exact le_trans (abs_add_le _ _) (add_le_add (le_trans ht.1 ha) ih.1)
      · rw [add_sub_assoc]
        exact le_trans (abs_add_le _ _) (add_le_add (le_trans ht.2 ha) ih.2)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.reach_le {T : Taylm n} {h C : ℝ} (h0 : 0 < h) (h1 : h ≤ 1)
    (hT : T.IsScaled h C) : -- --- CONCL ---
    T.reach T.constCoef ≤ 2 * C * h := by -- --- PROOF ---
  obtain ⟨w, i, s⟩ := hT
  have hb := Taylm.aux_abs_polyBounds_sub_le T.terms h0 h1
  have hp : h ^ (T.maxOrder + 1) ≤ h := pow_le_of_le_one h0.le h1 (Nat.succ_ne_zero _)
  have hC : 0 ≤ C := le_trans (Taylm.weight_nonneg _ h0) w
  have hW : h * Taylm.weight T.terms h ≤ h * C := mul_le_mul_of_nonneg_left w h0.le
  have hr : C * h ^ (T.maxOrder + 1) ≤ C * h := mul_le_mul_of_nonneg_left hp hC
  unfold Taylm.reach Taylm.bounds Taylm.constCoef
  -- each end: the polynomial's part, then the remainder's
  refine max_le ?_ ?_
  · rw [show (Taylm.polyBounds T.terms).inf + T.rem.inf
        - ((T.terms.filter fun a => Taylm.degree a.2 == 0).map Prod.fst).sum
        = ((Taylm.polyBounds T.terms).inf
          - ((T.terms.filter fun a => Taylm.degree a.2 == 0).map Prod.fst).sum) + T.rem.inf by ring]
    exact le_trans (abs_add_le _ _) (by linarith [hb.1])
  · rw [show (Taylm.polyBounds T.terms).sup + T.rem.sup
        - ((T.terms.filter fun a => Taylm.degree a.2 == 0).map Prod.fst).sum
        = ((Taylm.polyBounds T.terms).sup
          - ((T.terms.filter fun a => Taylm.degree a.2 == 0).map Prod.fst).sum) + T.rem.sup by ring]
    exact le_trans (abs_add_le _ _) (by linarith [hb.2])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
