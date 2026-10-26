module

public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.IsBoundedDropEqsMinkDiffOf
public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct

@[expose] public section

/-!
# `Alg. 3` line 11: the eroded polytope, converted

`maxBackReachCZ`: one operand `CZ(P ⊖ Ẑ_W(τ_k))`, `P ∈ {P₁, P₂}`, of [1, Alg. 3] line 11,
`CZ ← conv(CZ(P₁ ⊖ Ẑ_W(τ_k)), CZ(P₂ ⊖ Ẑ_W(τ_k)))`: the polytope eroded by (11) and converted
by [1, Alg. 1]. The hull is taken in `LinearSys.maxBackReachStep`. `ρ` answers for bounded
polytopes only, as no oracle answers for all; the eroded polytope is bounded since `P`'s inequality
rows bound `P` and `Ẑ_W(τ_k)` holds its center.

## Inputs
* `ρ` – support oracle for bounded polytopes
* `P` – polytope
* `ZW` – disturbance zonotope

## Hypotheses
* `hP` – the inequality rows of `P` bound it

## Output
* constrained zonotope of the eroded polytope
## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       19-September-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3] line 11, one operand: `CZ(P ⊖ Ẑ_W(τ_k))`, the eroded polytope converted by
[1, Alg. 1]. -/
noncomputable def LinearSys.maxBackReachCZ
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (_ : Bornology.IsBounded P.construct)
      (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P : HPolytope (Vec ℝ n)) (hP : Bornology.IsBounded P.dropEqs.construct)
    (ZW : Zonotope (Vec ℝ n)) : ConZonotope (Vec ℝ n) :=
  -- 11. P ⊖ Ẑ_W(τ_k), (11)
  let P_ZW := P.minkDiffOf ZW.construct fun j => ZW.supportBound (P.A j)
  have hP_ZW : Bornology.IsBounded P_ZW.construct :=                 -- bounded, so `ρ` answers
    (HPolytope.isBounded_dropEqs_minkDiffOf _ hP ⟨ZW.c, ZW.center_mem_construct⟩).subset
      P_ZW.construct_subset_dropEqs
  -- 11. CZ(P ⊖ Ẑ_W(τ_k))
  HPolytope.conZonotope (P := P_ZW)                                   -- box, by Alg. 1
    (fun j => ρ P_ZW hP_ZW (LinearMap.proj j)) (fun j => ρ P_ZW hP_ZW (-LinearMap.proj j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
