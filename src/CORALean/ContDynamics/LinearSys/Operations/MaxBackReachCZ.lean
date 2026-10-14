module

public import CORALean.ContSet.Conversion.Real.HPolytope_to_ConZonotope
public import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf
public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound

@[expose] public section

/-!
# `Alg. 3` line 11: the eroded polytope, converted

`maxBackReachCZ`: one operand `CZ(P ⊖ Ẑ_W(τ_k))`, `P ∈ {P₁, P₂}`, of [1, Alg. 3] line 11,
`CZ ← conv(CZ(P₁ ⊖ Ẑ_W(τ_k)), CZ(P₂ ⊖ Ẑ_W(τ_k)))`: the polytope eroded by (11) and converted
by [1, Alg. 1]. The hull is taken in `LinearSys.maxBackReachStep`.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3] line 11, one operand: `CZ(P ⊖ Ẑ_W(τ_k))`, the eroded polytope converted by
[1, Alg. 1]. -/
noncomputable def LinearSys.maxBackReachCZ
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P : HPolytope (Vec ℝ n)) (ZW : Zonotope (Vec ℝ n)) : ConZonotope (Vec ℝ n) :=
  let P_ZW := P.minkDiffOf ZW.construct fun j => ZW.supportBound (P.A j) -- 11. P ⊖ Ẑ_W(τ_k), (11)
  HPolytope.conZonotope (P := P_ZW)                                       -- 11. CZ(P ⊖ Ẑ_W(τ_k))
    (fun j => ρ P_ZW (LinearMap.proj j)) (fun j => ρ P_ZW (-LinearMap.proj j))  -- box, by Alg. 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
