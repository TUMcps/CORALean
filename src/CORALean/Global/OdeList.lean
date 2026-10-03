import CORALean.Global.EvalList
import CORALean.Global.ElementaryDerivBounds
import Mathlib.Algebra.Polynomial.Roots

/-!
# `odePoly` on integer coefficient lists

`odeL q k` is `odePoly q k` with `q` and the result as lists of integer coefficients, lowest
degree first: the computable form of the derivative polynomials of `tan` and `tanh`
(`q = 1 + X²`, `1 - X²`). The theorem is that the two evaluate alike.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Polynomial


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Coefficientwise sum. -/
private def aux_addL : List ℤ → List ℤ → List ℤ
  | [], l => l
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: aux_addL l m

/-- Product of two coefficient lists. -/
private def aux_mulL : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: q, l => aux_addL (l.map (a * ·)) (0 :: aux_mulL q l)

/-- Derivative: `(a + X r)' = r + X r'`. -/
private def aux_derL : List ℤ → List ℤ
  | [] => []
  | _ :: l => aux_addL l (0 :: aux_derL l)

/-- The polynomial a list stands for. -/
private noncomputable def aux_toPoly : List ℤ → ℝ[X]
  | [] => 0
  | a :: l => C (a : ℝ) + X * aux_toPoly l

private theorem aux_toPoly_add (a b : List ℤ) :
    aux_toPoly (aux_addL a b) = aux_toPoly a + aux_toPoly b := by -- --- PROOF ---
  induction a generalizing b with
  | nil => simp [aux_addL, aux_toPoly]
  | cons a l ih =>
    cases b with
    | nil => simp [aux_addL, aux_toPoly]
    | cons b m => simp only [aux_addL, aux_toPoly, ih]; push_cast; simp only [map_add]; ring

private theorem aux_toPoly_smul (c : ℤ) (l : List ℤ) :
    aux_toPoly (l.map (c * ·)) = C (c : ℝ) * aux_toPoly l := by
  induction l with
  | nil => simp [aux_toPoly]
  | cons a l ih => simp only [List.map, aux_toPoly, ih]; push_cast; simp only [map_mul]; ring

private theorem aux_toPoly_mul (q l : List ℤ) :
    aux_toPoly (aux_mulL q l) = aux_toPoly q * aux_toPoly l := by -- --- PROOF ---
  induction q with
  | nil => simp [aux_mulL, aux_toPoly]
  | cons a q ih =>
    simp only [aux_mulL, aux_toPoly_add, aux_toPoly_smul, aux_toPoly, ih]
    simp only [Int.cast_zero, map_zero, zero_add]
    ring

private theorem aux_toPoly_der (l : List ℤ) :
    derivative (aux_toPoly l) = aux_toPoly (aux_derL l) := by -- --- PROOF ---
  induction l with
  | nil => simp [aux_derL, aux_toPoly]
  | cons a l ih =>
    simp only [aux_derL, aux_toPoly_add, aux_toPoly, derivative_add, derivative_C,
      derivative_mul, derivative_X, ih]
    simp only [Int.cast_zero, map_zero, zero_add]
    ring

private theorem aux_eval_toPoly (l : List ℤ) (x : ℝ) :
    (aux_toPoly l).eval x = evalL l x := by
  induction l with
  | nil => simp [aux_toPoly, evalL]
  | cons a l ih => simp [aux_toPoly, evalL, ih]


-- =====================================  MAIN DEFINITION  ====================================== --

def odeL (q : List ℤ) : ℕ → List ℤ
  | 0 => [0, 1]
  | k + 1 => aux_mulL (aux_derL (odeL q k)) q

theorem eval_odePoly_odeL {q : List ℤ} {Q : ℝ[X]} (hQ : ∀ x, Q.eval x = evalL q x) (k : ℕ)
    (x : ℝ) : (odePoly Q k).eval x = evalL (odeL q k) x := by -- --- PROOF ---
  have hQ' : Q = aux_toPoly q :=
    Polynomial.funext fun x => by rw [hQ, aux_eval_toPoly]
  have key : ∀ k, odePoly Q k = aux_toPoly (odeL q k) := by
    intro k
    induction k with
    | zero => simp [odePoly, odeL, aux_toPoly]
    | succ k ih => rw [odePoly, odeL, aux_toPoly_mul, ← aux_toPoly_der, ih, hQ']
  rw [key, aux_eval_toPoly]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
