module

public import CORALean.ContSet.Zonotope.Real.Operations.SortByLength

@[expose] public section

/-!
# `sortByLength` sorts by decreasing 2-norm

`‖g_{s,i}‖₂ ≥ ‖g_{s,i+1}‖₂` for the sorted generators, as [1, Sec. III-B, Step 1)] requires.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* sorted generator lengths are nonincreasing

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The sorted generator lengths are antitone. -/
theorem Zonotope.antitone_generatorLength_sortByLength (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    Antitone fun i => Z.sortByLength.generatorLength i := by -- --- PROOF ---
  -- `Tuple.sort` makes the negated lengths monotone
  intro i j hij
  have h := Tuple.monotone_sort (fun j => -Z.generatorLength j) hij
  simp only [Zonotope.generatorLength, Zonotope.sortByLength, Function.comp] at h ⊢
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
