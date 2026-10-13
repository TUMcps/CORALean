module

public import CORALean.ContSet.Taylm.Real.Taylm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

/-!
# A term list re-expanded about a point

`P(m + r ⊙ s)` as a polynomial in `s`: each factor `(mₖ + rₖ sₖ)^{eₖ}` by the binomial theorem,
the product of the sums as a sum over the exponent vectors `j ≤ e`. The `reexp(·)` of [1, Alg. 1]
(lines 15, 22, 28), here with the scaling `r` that maps the new expansion point's box onto the
normalized one.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.reexpTerms (m r : Vec ℝ n) (L : List (ℝ × (Fin n → ℕ))) :
    List (ℝ × (Fin n → ℕ)) :=
  L.flatMap fun a => (Fintype.piFinset fun k => Finset.range (a.2 k + 1)).toList.map fun j =>
    (a.1 * ∏ k, ((a.2 k).choose (j k) : ℝ) * m k ^ (a.2 k - j k) * r k ^ (j k), j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
