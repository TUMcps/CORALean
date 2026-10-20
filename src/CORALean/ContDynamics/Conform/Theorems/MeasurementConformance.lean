module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# [1, Sec. 2]: what a noisy measurement can certify

The exact output lies somewhere in `y ⊕ V`, `y` the measurement and `V` the set of
measurement errors. If `y ⊕ V` lies in an inner approximation of the reachable set, the
exact output is reachable (measurement conformance); if `y ⊕ V` misses an outer
approximation, it is not (a falsification). Neither needs the exact reachable set,
which is the point of Fig. 2.

## Inputs
* `α` – additive group
* `R` – exact reachable set
* `Ru` – inner approximation
* `Ro` – outer approximation
* `V` – error set
* `y` – measurement
* `yt` – exact output

## Hypotheses
* `hyt` – exact output lies in `y ⊕ V`

## Conclusion
* an inner approximation certifies reachability, an outer one refutes it

## References

* [1] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 2]: `y ⊕ V` inside an inner approximation certifies the exact output, outside
an outer one refutes it. -/
theorem Conform.measurement_conformance {α : Type} [AddCommGroup α] (R Ru Ro V : Set α)
    (y yt : α) (hyt : yt ∈ {y} + V) :
    (Ru ⊆ R → {y} + V ⊆ Ru → yt ∈ R) ∧
      (R ⊆ Ro → Disjoint ({y} + V) Ro → yt ∉ R) :=
  ⟨fun hu hin => hu (hin hyt), fun ho hdis hR => Set.disjoint_left.mp hdis hyt (ho hR)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
