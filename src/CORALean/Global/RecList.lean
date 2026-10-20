module

public import CORALean.Global.OdeList

@[expose] public section

/-!
# The derivative polynomials of `atan` and `asin` on integer coefficient lists

`recL q s j` is the polynomial of the recursion `P₀ = 1`, `Pⱼ₊₁ = Pⱼ' · q + sⱼ · X · Pⱼ`, as a
list of integer coefficients, lowest degree first: the computable form of `atanPoly`,
`atanDom`, `asinPoly` and `asinDom` (`q = 1 ± X²`, `sⱼ = ∓2(j+1)`, `2j+1`). The theorem is that
any polynomial sequence with this recursion evaluates as the list does.

## Inputs
* `q` – coefficient list of the factor
* `s` – coefficients of the linear term

## Output
* the function giving the coefficient list of each recursion order
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Polynomial


-- =====================================  MAIN DEFINITION  ====================================== --

def recL (q : List ℤ) (s : ℕ → ℤ) : ℕ → List ℤ
  | 0 => [1]
  | j + 1 => addL (mulL (derL (recL q s j)) q) ((0 :: recL q s j).map (s j * ·))

theorem eval_recL {q : List ℤ} {Q : ℝ[X]} (hQ : ∀ x, Q.eval x = evalL q x) (s : ℕ → ℤ)
    (P : ℕ → ℝ[X]) (h0 : P 0 = 1)
    (hs : ∀ j, P (j + 1) = derivative (P j) * Q + C ((s j : ℤ) : ℝ) * (X * P j)) (j : ℕ)
    (x : ℝ) : -- --- CONCL ---
    (P j).eval x = evalL (recL q s j) x := by -- --- PROOF ---
  have hQ' : Q = toPolyL q := Polynomial.funext fun x => by rw [hQ, eval_toPolyL]
  have key : ∀ j, P j = toPolyL (recL q s j) := by
    intro j
    induction j with
    | zero => simp [h0, recL, toPolyL]
    | succ j ih =>
      rw [hs, recL, toPolyL_add, toPolyL_mul, ← toPolyL_der, ← ih, hQ', toPolyL_smul]
      simp only [toPolyL, Int.cast_zero, map_zero, zero_add]
      rw [← ih]
  rw [key, eval_toPolyL]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
