module

public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeHPolytopeFacetsContains
public import CORALean.ContSet.HPolytope.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ConstructEqIInter

@[expose] public section

/-!
# A float bundle lies in CORA's `polytope(zB)`

Each member lies in its facet polytope (`Zonotope.hPolytopeFacets_contains`), the whole space holds
every point, and an intersection holds what both its operands hold (`intersection_outer`), so a
point of every member is a point of the fold.

## Inputs
* `p` – Newton steps per row length
* `zB` – zonotope bundle

## Hypotheses
* none

## Conclusion
* bundle is contained in its intersected facet polytopes
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of the start and of every listed polytope is a point of the folded intersection. -/
private theorem aux_mem_foldl (L : List (HPolytope 𝕋 (Vec 𝕋 (n + 1))))
    (P₀ : HPolytope 𝕋 (Vec 𝕋 (n + 1))) {x : Vec ℝ (n + 1)} (h₀ : x ∈ P₀.construct)
    (hL : ∀ P ∈ L, x ∈ P.construct) :
    x ∈ (L.foldl HPolytope.intersection P₀).construct := by -- --- PROOF ---
  induction L generalizing P₀ with
  | nil => exact h₀
  | cons P L ih =>
    exact ih _ (HPolytope.intersection_outer P₀ P ⟨h₀, hL P List.mem_cons_self⟩)
      fun Q hQ => hL Q (List.mem_cons_of_mem P hQ)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float bundle lies in its members' facet polytopes, intersected. -/
theorem ZonoBundle.hPolytopeAll_contains (p : ℕ) (zB : ZonoBundle (Vec 𝕋 (n + 1))) :
    zB.construct ⊆ (zB.hPolytopeAll p).construct := by -- --- PROOF ---
  intro x hx
  rw [ZonoBundle.construct_eq_iInter, Set.mem_iInter] at hx
  -- the whole space, then each member's rows
  refine aux_mem_foldl _ _ ⟨x, ⟨fun i => i.elim0, fun i => i.elim0⟩, 0, ?_, add_zero x⟩ ?_
  · exact fun i => ⟨le_of_eq toReal_zero, le_of_eq toReal_zero.symm⟩
  · intro P hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    exact (zB.Z i).hPolytopeFacets_contains p (hx i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
