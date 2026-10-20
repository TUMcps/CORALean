module

public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConInt
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCoef

@[expose] public section

/-!
# The integer selector row is the exact one, scaled

`unionConInt` is `4 max(1,p₁) max(1,p₂)` times the exact layer's selector coefficients,
column by column. A column of a group exists only when its operand has a factor, which is
where the quotient the scale cancels is non-zero.

## Inputs
* `p₁` – factor count of first operand
* `p₂` – factor count of second operand
* `l` – coefficient index

## Hypotheses
* none

## Conclusion
* the integer coefficient is the scaled exact coefficient
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.unionConInt_eq (p₁ p₂ : ℕ)
    (l : Fin (2 + (p₁ + p₁ + (p₂ + p₂ + (p₁ * p₂ + p₁ * p₂))))) :
    (4 * ((max 1 p₁ : ℕ) : ℝ) * ((max 1 p₂ : ℕ) : ℝ)) * Real.ConPolyZono.unionConCoef p₁ p₂ l
      = (ConPolyZono.unionConInt p₁ p₂ l : ℝ) := by -- --- PROOF ---
  -- the cases `max` resolves to the count itself, which a column's existence forces
  have h1 : ∀ _ : Fin p₁, ((max 1 p₁ : ℕ) : ℝ) = p₁ := fun j => by
    rw [max_eq_right (by have := j.pos; omega)]
  have h2 : ∀ _ : Fin p₂, ((max 1 p₂ : ℕ) : ℝ) = p₂ := fun j => by
    rw [max_eq_right (by have := j.pos; omega)]
  -- the two leading columns, then the four groups in turn
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · fin_cases l <;> simp [ConPolyZono.unionConInt, Real.ConPolyZono.unionConCoef]
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · -- the groups over the first operand's factors
    refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    all_goals
      have hp : (0 : ℝ) < p₁ := by exact_mod_cast j.pos
      simp only [ConPolyZono.unionConInt, Real.ConPolyZono.unionConCoef, Fin.append_left,
        Fin.append_right, h1 j]
      push_cast
      field_simp
      ring
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    all_goals
      have hp : (0 : ℝ) < p₂ := by exact_mod_cast j.pos
      simp only [ConPolyZono.unionConInt, Real.ConPolyZono.unionConCoef, Fin.append_left,
        Fin.append_right, h2 j]
      push_cast
      field_simp
      ring
  · -- the cross group: both counts positive, as the column indexes a product
    refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    all_goals
      have hpq : 0 < p₁ * p₂ := j.pos
      have hp1 : 0 < p₁ := Nat.pos_of_mul_pos_right hpq
      have hq1 : 0 < p₂ := Nat.pos_of_mul_pos_left hpq
      have hp : (0 : ℝ) < p₁ := by exact_mod_cast hp1
      have hq : (0 : ℝ) < p₂ := by exact_mod_cast hq1
      rw [max_eq_right (by omega : 1 ≤ p₁), max_eq_right (by omega : 1 ≤ p₂)]
      simp only [ConPolyZono.unionConInt, Real.ConPolyZono.unionConCoef, Fin.append_left,
        Fin.append_right]
      push_cast
      field_simp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
