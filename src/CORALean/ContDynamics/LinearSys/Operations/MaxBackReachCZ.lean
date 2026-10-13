import CORALean.ContSet.Conversion.Real.HPolytope_to_ConZonotope
import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf
import CORALean.ContSet.Zonotope.Real.Operations.SupportBound

/-!
# `Alg. 2` line 11: the eroded polytope, converted

`maxBackReachCZ`: [1, Alg. 2] line 11, `CZ(P ⊖ Ẑ_W(τ_k))`, the eroded polytope converted by
(17).

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 11: `CZ(P ⊖ Ẑ_W(τ_k))`, the eroded polytope converted by (17). -/
noncomputable def LinearSys.maxBackReachCZ
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P : HPolytope (Vec ℝ n)) (ZW : Zonotope (Vec ℝ n)) : ConZonotope (Vec ℝ n) :=
  let Q := P.minkDiffOf ZW.construct fun i => ZW.supportBound (P.A i)   -- ⊖ Ẑ_W(τ_k)
  HPolytope.conZonotope (P := Q)
    (fun j => ρ Q (LinearMap.proj j)) (fun j => ρ Q (-LinearMap.proj j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
