module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalOn

@[expose] public section

/-!
# The whole factor box evaluates to the whole set

`subsetAt_unitBox` needs `q = 0` to say this; `evalOn` carries the independent
block itself, so the same statement holds of every polynomial zonotope: the
whole of [1, Def. 3] and not only its dependent half. It is what turns an
argument's `construct` into an `evalOn` and back, which is how a set added to an
evaluated one is read in Lean.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* evaluation on the whole factor box is the set

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Holding the factors in their whole box is holding them nowhere: the
evaluation is the set. -/
theorem PolyZonotope.evalOn_unitBox (pZ : PolyZonotope α) :
    pZ.evalOn {a | ∀ k, |a k| ≤ 1} = pZ.construct := by -- --- PROOF ---
  ext x
  constructor
  · -- the evaluation's witness is the set's, `point` being the dependent half
    rintro ⟨a, ha, β, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, rfl⟩
  · rintro ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, ha, β, hβ, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
