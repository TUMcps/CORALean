module

public import CORALean.HybridDynamics.Definitions.UrgentRun

@[expose] public section

/-!
# An urgent run is a run

[1, Def. 1]'s urgent runs are among `Run`'s: forgetting that each stay meets no guard before
its end leaves a run. So every enclosure proved of `Run`'s reachable states, the invariant-free
automaton's included, holds of the urgent semantics too.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 1]: an urgent run is a run. -/
theorem HybridAutomaton.UrgentRun.toRun {HA : HybridAutomaton S G L 𝕋 n} {ℓ ℓ' : L}
    {x y : Vec ℝ n} (h : HA.UrgentRun ℓ x ℓ' y) : HA.Run ℓ x ℓ' y := by
  induction h with
  | flow h _ => exact .flow h
  | jump h _ hmem hguard _ ih => exact .jump h hmem hguard ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
