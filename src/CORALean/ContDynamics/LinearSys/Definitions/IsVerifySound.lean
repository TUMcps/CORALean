module

public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifySpec
public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# What `Alg. 3`'s passed-in functions must satisfy

`verify` takes `reachFn`, `innerApprox`, the two distances and the comparison `le` as parameters in
[1, Alg. 3], so its soundness is relative to what they promise. Written for a set `Reach` of states
reached by some trajectory: `reachFn ε` is an outer approximation of `Reach` for every `ε`;
`innerApprox R ε` lies inside `Reach`; `distG C P ≤ 0` means `C ⊆ P` and `0 < distG C P` that it
does not; `0 < distF C P` means `C` misses `P` and `distF C P ≤ 0` that it meets it; `le` decides
`≤`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- What the verification algorithm needs of the functions passed in: the reachable-set
approximations enclose or lie inside `Reach`, and the sign of each distance decides containment in,
or disjointness from, a polytope. -/
structure LinearSys.IsVerifySound (Reach : Set (Vec ℝ n)) (reachFn : ℝ → Zonotope (Vec ℝ n))
    (innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n))
    (distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ)
    (le : ℝ → ℝ → Bool) : Prop where
  le_iff (a b : ℝ) : le a b = true ↔ a ≤ b
  outer (ε : ℝ) : Reach ⊆ (reachFn ε).construct
  inner (R : Zonotope (Vec ℝ n)) (ε : ℝ) : (innerApprox R ε).construct ⊆ Reach
  distG_nonpos (C : ConZonotope (Vec ℝ n)) (P : HPolytope (Vec ℝ n)) :
    distG C P ≤ 0 → C.construct ⊆ P.construct
  distG_pos (C : ConZonotope (Vec ℝ n)) (P : HPolytope (Vec ℝ n)) :
    0 < distG C P → ¬ C.construct ⊆ P.construct
  distF_pos (C : ConZonotope (Vec ℝ n)) (P : HPolytope (Vec ℝ n)) :
    0 < distF C P → Disjoint C.construct P.construct
  distF_nonpos (C : ConZonotope (Vec ℝ n)) (P : HPolytope (Vec ℝ n)) :
    distF C P ≤ 0 → ¬ Disjoint C.construct P.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
