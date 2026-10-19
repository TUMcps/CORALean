module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Augment
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Powers of the augmented matrix on the last unit vector

The identity behind [1, Lemma IV.1]: `C̃ = [A u; 0 0]` maps `[x; c]` to `[Ax + cu; 0]`, so
`C̃^{k+1} [0ₙ; 1] = [Aᵏ u; 0]`. It reads the exponential of `C̃` on `[0ₙ; 1]` as the input
solution, and the Krylov Taylor terms of [1, Thm. IV.2] as `A^{j-1} u`.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The first `n` rows of `C̃ z`: `A` on the first `n` coordinates plus the last one times `u`. -/
theorem Krylov.aux_augment_mulVec_castSucc (A : Mat ℝ n n) (u : Vec ℝ n)
    (z : Fin (n + 1) → ℝ) (i : Fin n) :
    (Krylov.augment A u *ᵥ z) (Fin.castSucc i)
      = (A *ᵥ fun j => z (Fin.castSucc j)) i + z (Fin.last n) * u i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, Krylov.augment, Matrix.of_apply,
    Fin.lastCases_castSucc, Fin.lastCases_last]
  ring

/-- The last row of `C̃` is zero. -/
theorem Krylov.aux_augment_mulVec_last (A : Mat ℝ n n) (u : Vec ℝ n) (z : Fin (n + 1) → ℝ) :
    (Krylov.augment A u *ᵥ z) (Fin.last n) = 0 := by
  simp [mulVec, dotProduct, Krylov.augment]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `C̃^{k+1} [0; 1] = [Aᵏ u; 0]`. -/
theorem Krylov.augment_pow_mulVec (A : Mat ℝ n n) (u : Vec ℝ n) (k : ℕ) : -- --- CONCL ---
    (fun j => (Krylov.augment A u ^ (k + 1) *ᵥ (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℝ))
        (Fin.castSucc j)) = A ^ k *ᵥ u
      ∧ (Krylov.augment A u ^ (k + 1) *ᵥ (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℝ))
        (Fin.last n) = 0 := by -- --- PROOF ---
  induction k with
  | zero =>
    have h0 : (fun j => (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℝ) (Fin.castSucc j)) = 0 :=
      funext fun j => Pi.single_eq_of_ne (Fin.castSucc_ne_last j) 1
    refine ⟨funext fun j => ?_, ?_⟩
    · rw [pow_one, Krylov.aux_augment_mulVec_castSucc, h0, mulVec_zero, pow_zero, one_mulVec]
      simp
    · rw [pow_one]
      exact Krylov.aux_augment_mulVec_last A u _
  | succ k ih =>
    -- one more `C̃` maps `[Aᵏ u; 0]` to `[A^{k+1} u; 0]`
    rw [pow_succ', ← mulVec_mulVec]
    refine ⟨funext fun j => ?_, Krylov.aux_augment_mulVec_last A u _⟩
    rw [Krylov.aux_augment_mulVec_castSucc, ih.2, ih.1, zero_mul, add_zero, pow_succ',
      ← mulVec_mulVec]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
