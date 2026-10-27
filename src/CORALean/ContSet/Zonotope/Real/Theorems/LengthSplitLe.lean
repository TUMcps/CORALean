module

public import CORALean.ContSet.Zonotope.Real.Operations.LengthSplit

@[expose] public section

/-!
# `lengthSplit` keeps the longest generators

Every generator `lengthSplit` keeps is at least as long, in the 2-norm, as every generator it drops:
the split of [1, Sec. IV-D, Step 1)] has `G_a` the generators of largest 2-norm.

## Inputs
* `Z` – zonotope
* `q` – kept count
* `l` – kept index
* `r` – dropped index

## Hypotheses
* `hq` – at most all generators

## Conclusion
* each kept generator is at least as long as each dropped one

## References

* [1] [L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the Order Reduction
      of Zonotopes". IEEE Control Systems Letters,
      2025.](../../../../../../references/2025/luetzow-lcss-underapprox-order-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real
open scoped CORALean
variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The kept generators are at least as long as the dropped ones. -/
theorem Zonotope.lengthSplit_le (Z : Zonotope (Vec ℝ n)) (q : ℕ) (hq : q ≤ Z.h)
    (l : Fin q) (r : Fin (Z.h - q)) : -- --- CONCL ---
    Z.generatorLength ((Z.lengthSplit q hq).right r)
      ≤ Z.generatorLength ((Z.lengthSplit q hq).left l) := by -- --- PROOF ---
  -- `Tuple.sort` makes the negated length monotone, and `left` precedes `right`
  have hm := Tuple.monotone_sort fun j => -Z.generatorLength j
  have h := @hm (finCongr (Nat.add_sub_cancel' hq).symm.symm (Fin.castAdd _ l))
    (finCongr (Nat.add_sub_cancel' hq).symm.symm (Fin.natAdd _ r)) (by simp [Fin.le_def]; omega)
  simp only [Function.comp] at h
  exact neg_le_neg_iff.mp h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
