import CORALean.ContDynamics.LinearARX.Operations.Aext
import CORALean.ContDynamics.LinearARX.Operations.Bext

/-!
# The time-varying input parameters

[1, Thm. 1], (9b): `B̃ᵢ(k) = ∑_{j=0}^{k-1} Ā_ext^j B̄_ext,i-j`, the weight of the input `ũ(k₊ - i)`
in the window `ỹ(k:k₊)`. `Ã(k) = Ā_ext^k` (9a) needs no definition of its own.
The index `i` is an integer so that Lemma 3's `B̄_ext,i+1-k` is a term, not a case split.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.Btilde (sys : LinearARX 𝕋 dy du p) (k : ℕ) (i : ℤ) : Mat ℝ (p * dy) du :=
  ∑ j ∈ Finset.range k, sys.Aext ^ j * sys.Bext (i - j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
