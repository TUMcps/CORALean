module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# Whether a neuron's bounds fit a merge bucket

[1, Def. 3]'s `I_k(i) ⊆ [y - δ, y + δ]`, decided by the caller's `le` — `FloatOps.le` for a
machine scalar, any order sound on a `true` for an exact one. The bucket's ends are widened
outward before the comparison, so a `true` still means containment after rounding.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 3]'s `I_k(i) ⊆ [y - δ, y + δ]`, decided by `le`. -/
def inMergeBucket (le : 𝕋 → 𝕋 → Bool) (I : Interval (Vec 𝕋 n)) (y δ : 𝕋) (i : Fin n) : Bool :=
  le (subDown y δ) (I.inf i) && le (I.sup i) (addUp y δ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
