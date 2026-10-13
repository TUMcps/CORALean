import CORALean.Specification.Specification

/-!
# A witness outside a safe set falsifies it

The exit an algorithm takes to report "unsafe" against a halfspace
specification: [1, Alg. 2, l. 9-10] halves the time step until a reachable
point's bound in some direction exceeds the safe set's offset there,
producing a point outside that halfspace and so outside `S` itself. Since
`Holds` for a safe set unfolds to `X ⊆ S`, one such point refutes it — the
counterpart to `Specification.holds_safeSet_of_bounds`, one certifying
safety, the other refuting it.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of `X` outside `S` refutes the safe-set specification for `X`. -/
theorem Specification.not_holds_safeSet_of_mem {S X : Set α} {x : α} (hx : x ∈ X) (hS : x ∉ S) :
    ¬ (Specification.safeSet S).Holds X :=
  fun h => hS (h hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
