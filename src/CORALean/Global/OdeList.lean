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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Coefficientwise sum. -/
def addL : List ℤ → List ℤ → List ℤ
  | [], l => l
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addL l m

/-- Product of two coefficient lists. -/
def mulL : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: q, l => addL (l.map (a * ·)) (0 :: mulL q l)

/-- Derivative: `(a + X r)' = r + X r'`. -/
def derL : List ℤ → List ℤ
  | [] => []
  | _ :: l => addL l (0 :: derL l)

/-- The polynomial a list stands for. -/
noncomputable def toPolyL : List ℤ → ℝ[X]
  | [] => 0
  | a :: l => C (a : ℝ) + X * toPolyL l

theorem toPolyL_add (a b : List ℤ) :
    toPolyL (addL a b) = toPolyL a + toPolyL b := by -- --- PROOF ---
  induction a generalizing b with
  | nil => simp [addL, toPolyL]
  | cons a l ih =>
    cases b with
    | nil => simp [addL, toPolyL]
    | cons b m => simp only [addL, toPolyL, ih]; push_cast; simp only [map_add]; ring

theorem toPolyL_smul (c : ℤ) (l : List ℤ) :
    toPolyL (l.map (c * ·)) = C (c : ℝ) * toPolyL l := by
  induction l with
  | nil => simp [toPolyL]
  | cons a l ih => simp only [List.map, toPolyL, ih]; push_cast; simp only [map_mul]; ring

theorem toPolyL_mul (q l : List ℤ) :
    toPolyL (mulL q l) = toPolyL q * toPolyL l := by -- --- PROOF ---
  induction q with
  | nil => simp [mulL, toPolyL]
  | cons a q ih =>
    simp only [mulL, toPolyL_add, toPolyL_smul, toPolyL, ih]
    simp only [Int.cast_zero, map_zero, zero_add]
    ring

theorem toPolyL_der (l : List ℤ) :
    derivative (toPolyL l) = toPolyL (derL l) := by -- --- PROOF ---
  induction l with
  | nil => simp [derL, toPolyL]
  | cons a l ih =>
    simp only [derL, toPolyL_add, toPolyL, derivative_add, derivative_C,
      derivative_mul, derivative_X, ih]
    simp only [Int.cast_zero, map_zero, zero_add]
    ring

theorem eval_toPolyL (l : List ℤ) (x : ℝ) :
    (toPolyL l).eval x = evalL l x := by
  induction l with
  | nil => simp [toPolyL, evalL]
  | cons a l ih => simp [toPolyL, evalL, ih]

def odeL (q : List ℤ) : ℕ → List ℤ
  | 0 => [0, 1]
  | k + 1 => mulL (derL (odeL q k)) q

theorem eval_odePoly_odeL {q : List ℤ} {Q : ℝ[X]} (hQ : ∀ x, Q.eval x = evalL q x) (k : ℕ)
    (x : ℝ) : (odePoly Q k).eval x = evalL (odeL q k) x := by -- --- PROOF ---
  have hQ' : Q = toPolyL q :=
    Polynomial.funext fun x => by rw [hQ, eval_toPolyL]
  have key : ∀ k, odePoly Q k = toPolyL (odeL q k) := by
    intro k
    induction k with
    | zero => simp [odePoly, odeL, toPolyL]
    | succ k ih => rw [odePoly, odeL, toPolyL_mul, ← toPolyL_der, ih, hQ']
  rw [key, eval_toPolyL]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
