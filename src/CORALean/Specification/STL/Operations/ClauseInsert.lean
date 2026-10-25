module

public import CORALean.Specification.STL.Operations.BranchMerge

@[expose] public section

/-!
# Adding a branch to a clause

[1, Lemma 2]: a branch joins the one of its own `j`, if the clause has one, and is appended
otherwise.

## Inputs
* `b` – branch to add

## Output
* the clause with the branch merged in or appended

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `b` merged into the branch of `cl` with the same `j`, or put at the end. -/
def STL.Clause.insert (b : STL.Branch X) : STL.Clause X → STL.Clause X
  | [] => [b]
  | b' :: rest =>
    if b'.j = b.j then STL.Branch.merge b' b :: rest else b' :: STL.Clause.insert b rest


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
