import CORALean.ContDynamics.LinearARX.Operations.InputMat

/-!
# The extended input matrices

`B̄_ext,i` of [1, Thm. 1], (10): `B̄ᵢ` in the last block row, zero above. Indexed by an integer
because [1] reads `B̄ᵢ = 0` for `i < 0` and `i > p` and then sums over shifted indices
(Eq. 9b, Lemma 3), so the zero outside `0 ≤ i ≤ p` is part of the definition.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.Bext (sys : LinearARX 𝕋 dy du p) (i : ℤ) : Mat ℝ (p * dy) du :=
  if h : 0 ≤ i ∧ i ≤ p then toRealMat (sys.inputMat ⟨i.toNat, by omega⟩) else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
