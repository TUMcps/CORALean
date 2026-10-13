import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce

/-!
# `PolyZonotope.reduceBox`: what a sub-box of the factors becomes under `reduce`

`reduce` merges columns and boxes generators into the independent block, neither
of which touches a factor; the one thing it does to the factor domain is drop
the factors no column reads any more, which renumbers the survivors by
`factorIdx`. This is `B` read through that renumbering — stated index by index,
since the two domains are equal in size but not in name. It is the half of
[1, Lemma 4]'s bookkeeping that [1] never states: its Table 1 omits `reduce`.

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

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same factor values `B` holds, read through the renumbering that dropping
the unused factors performs. -/
def PolyZonotope.reduceBox (pZ : PolyZonotope (Vec ℝ n)) (o : ℕ) (B : Set (Fin pZ.p → ℝ)) :
    Set (Fin (pZ.reduce o).p → ℝ) :=
  {a' | ∃ a ∈ B, ∀ (k : Fin (pZ.reduce o).p) (k' : Fin pZ.compact.p),
    (k : ℕ) = (k' : ℕ) → a' k = a (PolyZonotope.factorIdx pZ.compactGens.E k')}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
