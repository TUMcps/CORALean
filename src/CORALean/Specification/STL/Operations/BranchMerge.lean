module

public import CORALean.Specification.STL.Definitions.SampledTime

@[expose] public section

/-!
# Merging two branches

`X_c^j(φ ∨ ϱ) ∨ X_c^j(φ' ∨ ϱ') ≡ X_c^j((φ ∨ φ') ∨ (ϱ ∨ ϱ'))`: two disjuncts at the same power `j`
of [1, Lemma 2]'s normal form become one, which is what keeps the `j` of a clause distinct.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The branch at `b.j` with the lists and the predicate of both. -/
def STL.Branch.merge (b b' : STL.Branch X) : STL.Branch X :=
  { j := b.j, ϱ := .or b.ϱ b'.ϱ, K := b.K ++ b'.K, L := b.L ++ b'.L }


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
