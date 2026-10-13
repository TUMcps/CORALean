module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalOnUnitBox
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceByEvalOn

@[expose] public section

/-!
# Boxing what two partitions drop over-approximates

`reduceBy_evalOn` read over the whole factor box, `evalOn_unitBox` turning each
side back into what it constructs. It holds at *every* pair of partitions, which
is what lets the ranking be a heuristic — Girard's metric appears nowhere here
or there.

Stated separately because almost every caller wants the set and not the
dependency: an order bound is a precision knob, and only [1, Lemma 4] needs to
know that the factors were left alone while the generators moved.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   18-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n d r dI rI : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Boxing what the two partitions drop over-approximates, whichever partitions
they are. -/
theorem PolyZonotope.reduceBy_outer (pZ : PolyZonotope (Vec ℝ n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) :
    pZ.construct ⊆ (pZ.reduceBy partD partI).construct := by
  rw [← PolyZonotope.evalOn_unitBox pZ,
    ← PolyZonotope.evalOn_unitBox (pZ.reduceBy partD partI)]
  exact PolyZonotope.reduceBy_evalOn pZ partD partI fun _ ha => ha

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
