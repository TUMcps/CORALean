import CORALean.Specification.STL.Operations.FactorMeet

/-!
# One pass of the inner loop of [1, Alg. 2]

Lines 7-13 of [1, Alg. 2] for one `(j, k)`: the unsafe factors `K` of every polytope `P_hjkl`
that the reachable set `R̃(jΔt/2)` meets (line 9), `W`, intersected with `V` (line 12), without
the empty polytopes (line 13). The test `R̃(jΔt/2) ∩ P ≠ ∅` is `meets`, the emptiness check of line
13 is `isEmpty`, and `unsafeSet` computes `K` by [1, Prop. 2]; each is a parameter, `meets` trusted
when it answers `false` and `isEmpty` when it answers `true`.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2, l. 7-13]: `V` met with the unsafe factors of the polytopes `Pjk` that `Rj` meets. -/
def STL.factorStep (Rj : Set S) (Pjk : List (Set S)) (unsafeSet : Set S → Set X)
    (meets : Set S → Set S → Bool) (isEmpty : Set X → Bool) (V : List (Set X)) :
    List (Set X) :=
  let W := (Pjk.filter fun Pl => meets Rj Pl).map unsafeSet -- lines 8-11
  let V' := STL.factorMeet V W -- line 12
  V'.filter fun v => !isEmpty v -- line 13

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
