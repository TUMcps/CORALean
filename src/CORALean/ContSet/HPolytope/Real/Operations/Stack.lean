import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.stack`

The constraint lists of a finite family laid end to end, rows of the first member
first: `HPolytope.intersection` for `s` members at once. It is the H-representation
of a zonotope bundle whose members each come with their own [1, Prop. 4].

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
