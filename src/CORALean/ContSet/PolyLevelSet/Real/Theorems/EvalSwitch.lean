module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.Switch
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `PolyLevelSet.switch`'s rows

A switched row is `P`'s own plus `(1 - σᵢ x^e) bᵢ / 2`: `P`'s where `x^e = σᵢ`, and `P`'s
polynomial part with no right-hand side where `x^e = -σᵢ`.

## Inputs
* `P` – polynomial level set
* `e` – exponent of the switching monomial
* `s` – sign of each row
* `x` – point
* `i` – row index

## Hypotheses
* none

## Conclusion
* a switched row is `P`'s row plus the weighted right-hand side
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Row `i` of the switched system is `P`'s plus `(1 - σᵢ x^e) bᵢ / 2`. -/
theorem PolyLevelSet.eval_switch (P : PolyLevelSet n) (e : Fin n → ℕ) (s : Fin P.m → Bool)
    (x : Vec ℝ n) (i : Fin P.m) :
    (P.switch e s).eval x i = P.eval x i
      + 2⁻¹ * (1 - (if s i then 1 else -1) * ∏ k, x k ^ e k) * P.b i := by -- --- PROOF ---
  show (∑ l : Fin (P.q + 1), (P.switch e s).A i l * PolyZonotope.monomial (P.switch e s).R x l)
      - 2⁻¹ * P.b i = (∑ l, P.A i l * PolyZonotope.monomial P.R x l) - P.b i + _
  rw [Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [PolyLevelSet.switch, PolyZonotope.monomial, Fin.append_left, Fin.append_right]
  cases s i <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
