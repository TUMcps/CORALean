module

public import Mathlib.Data.Matrix.Mul
public import CORALean.ContSet.Taylm.Real.Operations.Mmul
public import CORALean.ContSet.Taylm.Real.Theorems.SumOuter
public import CORALean.ContSet.Taylm.Real.Theorems.TimesOuter

@[expose] public section

/-!
# `Taylm.mmul` encloses the matrix product

Entry `(i, j)` encloses the `(i, j)` entry of the product of the matrices of the enclosed
functions, pointwise.

## Inputs
* `a` – rows of the first matrix
* `b` – shared dimension
* `c` – columns of the second matrix
* `A` – first matrix of models
* `B` – second matrix of models
* `F` – first matrix of functions
* `G` – second matrix of functions
* `i` – row index
* `j` – column index

## Hypotheses
* `hA` – each entry of the first matrix encloses its function
* `hB` – each entry of the second matrix encloses its function

## Conclusion
* the product entry encloses the product of the functions
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.mmul_outer {a b c : ℕ} {A : Fin a → Fin b → Taylm n} {B : Fin b → Fin c → Taylm n}
    {F : Fin a → Fin b → Vec ℝ n → ℝ} {G : Fin b → Fin c → Vec ℝ n → ℝ}
    (hA : ∀ i k, (A i k).Encloses (F i k)) (hB : ∀ k j, (B k j).Encloses (G k j)) (i : Fin a)
    (j : Fin c) : -- --- CONCL ---
    (Taylm.mmul A B i j).Encloses fun t =>
      (Matrix.of (fun i k => F i k t) * Matrix.of (fun k j => G k j t)) i j := by -- --- PROOF ---
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact Taylm.sum_outer fun k => Taylm.times_outer (hA i k) (hB k j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
