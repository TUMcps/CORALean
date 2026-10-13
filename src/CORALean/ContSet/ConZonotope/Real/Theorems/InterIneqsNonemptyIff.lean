import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff

/-!
# A constrained zonotope meets a halfspace polytope exactly when the optimum is `≤ 0`

[1, Prop. 8]: `⟨C,d⟩_H` and `CZ` intersect if `ν ≤ 0`, `ν` the optimum of
`min δ` over `C(i,·)x − d(i) ≤ δ`, `x = c + Gα`, `Aα = b`, `α ∈ [−1,1]`. The constraints on
`(x, α)` are `ConZonotope.construct`, so the program's feasible objective values are the `δ` some
point of `CZ` keeps every halfspace slack under, and that is the set `ν` is least in.

Printed as a one-way `if`, and it is in fact an equivalence: `ν ≤ 0` is the paper's own argument,
and the converse only needs `δ = 0` to be feasible at a point of the intersection. So the
equivalence is stated, and the `if` direction is the half the verification algorithm calls.

`ν` is a hypothesis (`IsLeast`), exactly as the paper's own `min` presupposes an optimum rather
than producing one. The presupposition is not idle here: with `CZ` empty the program is infeasible
and has no optimum, while a junk value for `min ∅` would read as `ν = 0` and claim an intersection
that is not there.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 8]: the intersection check, `ν` the optimum of the paper's linear program. -/
theorem ConZonotope.inter_ineqs_nonempty_iff (cZ : ConZonotope (Vec ℝ n)) (C : Mat ℝ q n)
    (d : Vec ℝ q) (ν : ℝ)
    (hν : IsLeast {δ : ℝ | ∃ x ∈ cZ.construct, ∀ i, (C *ᵥ x) i - d i ≤ δ} ν) :
    (cZ.construct ∩ (HPolytope.ineqs C d).construct).Nonempty ↔ ν ≤ 0 := by -- --- PROOF ---
  constructor
  -- a shared point makes `δ = 0` feasible, so the least feasible `δ` is no larger
  · rintro ⟨x, hxZ, hxP⟩
    refine hν.2 (show (0 : ℝ) ∈ _ from ⟨x, hxZ, fun i => ?_⟩)
    have := HPolytope.mem_ineqs_iff.mp hxP i
    linarith
  -- the paper's direction: the optimum is attained, and its point lies in both sets
  · intro h0
    obtain ⟨x, hx, hle⟩ := hν.1
    refine ⟨x, hx, HPolytope.mem_ineqs_iff.mpr fun i => ?_⟩
    have := hle i
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
