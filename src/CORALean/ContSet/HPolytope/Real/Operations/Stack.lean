module

public import CORALean.ContSet.HPolytope.Real.HPolytope

@[expose] public section

/-!
# `HPolytope.stack`

The constraint lists of a finite family laid end to end, rows of the first member
first: `HPolytope.intersection` for `s` members at once. It is the H-representation
of a zonotope bundle whose members each come with their own [1, Prop. 4].

## Inputs
* `P` – H-polytopes indexed by `Fin s`

## Output
* the polytope with the constraint lists of all members laid end to end

## References

* [1] [M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.](../../../../../../references/2011/althoff-cdc-zonotope-bundles.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {s : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.stack (P : Fin s → HPolytope α) : HPolytope α where
  m := ∑ i, (P i).m
  A := fun r => (P (finSigmaFinEquiv.symm r).1).A (finSigmaFinEquiv.symm r).2
  b := fun r => (P (finSigmaFinEquiv.symm r).1).b (finSigmaFinEquiv.symm r).2
  me := ∑ i, (P i).me
  Ae := fun r => (P (finSigmaFinEquiv.symm r).1).Ae (finSigmaFinEquiv.symm r).2
  be := fun r => (P (finSigmaFinEquiv.symm r).1).be (finSigmaFinEquiv.symm r).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
