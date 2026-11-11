module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ResidualNormFloat
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# The computed residual bound covers the residual of the stored basis

The real residual of column `j` of the Krylov identity [1, Alg. 1], `(A v(j))_r - Σ_{i ≤ j+1}
h_{i,j} v(i)_r` read from the stored floats, lies between the two roundings `lo`, `hi`, so its
magnitude is at most `Krylov.residualColumnFloat` and its Euclidean norm at most
`Krylov.residualNormFloat`.

## Inputs
* `p` – Newton steps per norm
* `A` – matrix
* `V` – basis vectors
* `H` – Hessenberg entries
* `j` – column

## Hypotheses
* none

## Conclusion
* the real residual's norm is at most the float bound

## References

* [1] [M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
      Krylov Subspace". IEEE Transactions on Automatic Control,
      2020.](../../../../../../references/2020/althoff-tac-krylov.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.residual_le_residualNormFloat (p : ℕ) (A : Mat 𝕋 n n) (V : ℕ → Vector 𝕋 n)
    (H : ℕ → ℕ → 𝕋) (j : ℕ) : -- --- CONCL ---
    ‖fun r => (toRealMat A *ᵥ fun l => toReal (V j)[l]) r -
        ∑ i : Fin (j + 2), toReal (H i j) * toReal (V i)[r]‖₂ ≤
      toReal (Krylov.residualNormFloat p A V H j) := by -- --- PROOF ---
  refine norm₂_le_normUp p fun r => ?_
  set vj : Vec 𝕋 n := fun l => (V j)[l] with hvj
  set d : ℝ := (toRealMat A *ᵥ fun l => toReal (vj l)) r with hd
  set s : ℝ := ∑ i : Fin (j + 2), toReal (H i j) * toReal (V i)[r] with hs
  -- the two roundings of the dot product and of the sum
  have h1 : toReal (dotDown (A r) vj) ≤ d := dotDown_le (A r) vj
  have h2 : d ≤ toReal (dotUp (A r) vj) := le_dotUp (A r) vj
  have h3 : s ≤ toReal (sumUp fun i : Fin (j + 2) => mulUp (H i j) (V i)[r]) :=
    le_trans (Finset.sum_le_sum fun i _ => mul_le_mulUp _ _) (sum_le_sumUp _)
  have h4 : toReal (sumDown fun i : Fin (j + 2) => mulDown (H i j) (V i)[r]) ≤ s :=
    le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun i _ => mulDown_le_mul _ _)
  -- `lo` and `hi` bracket the exact entry
  have hlo := subDown_le_sub (dotDown (A r) vj)
    (sumUp fun i : Fin (j + 2) => mulUp (H i j) (V i)[r])
  have hhi := sub_le_subUp (dotUp (A r) vj)
    (sumDown fun i : Fin (j + 2) => mulDown (H i j) (V i)[r])
  have hmax : |d - s| ≤ max |toReal (subDown (dotDown (A r) vj)
      (sumUp fun i : Fin (j + 2) => mulUp (H i j) (V i)[r]))|
      |toReal (subUp (dotUp (A r) vj)
      (sumDown fun i : Fin (j + 2) => mulDown (H i j) (V i)[r]))| := by
    -- so the magnitude is at most the larger of the two
    rcases le_total 0 (d - s) with h | h
    · rw [abs_of_nonneg h]
      exact le_max_of_le_right ((by linarith : d - s ≤ _).trans (le_abs_self _))
    · rw [abs_of_nonpos h]
      exact le_max_of_le_left ((by linarith : -(d - s) ≤ _).trans (neg_le_abs _))
  show |d - s| ≤ |toReal (maximum _ _)|
  rw [toReal_maximum, toReal_absolute, toReal_absolute]
  exact hmax.trans (le_abs_self _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
