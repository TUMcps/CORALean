module

public import CORALean.ContSet.ConZonotope.Real.Theorems.ExistsConstructEqIffHPolytope
public import Mathlib.Tactic.Linarith
public import CORALean.ContSet.Conversion.Real.Theorems.StarSetConZonotopeExact
public import CORALean.ContSet.HPolytope.Real.Operations.ConstructEmptySet

@[expose] public section

/-!
# Every star set is a halfspace description

A star set is the image of the polytope of its factors under an affine map, and an image of a
polytope is one (Fourier–Motzkin), so there is no construction to give: the halfspace description is
found, not computed. It is reached through the constrained zonotope the star set is exactly
(`StarSet.conZonotope_exact`) and the theorem that these are the bounded halfspace descriptions
(`ConZonotope.exists_construct_eq_iff_hPolytope`); a crossed factor box denotes `∅`, which one
row cuts out.

## Inputs
* `s` – halfspace-predicate star set

## Hypotheses
* none

## Conclusion
* some halfspace polytope equals the star set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.exists_hPolytope_exact (s : StarSet ℋ𝒫 n) : -- --- CONCL ---
    ∃ P : HPolytope (Vec ℝ n), P.construct = s.construct := by -- --- PROOF ---
  by_cases hlu : ∀ k, s.dom.inf k ≤ s.dom.sup k
  · -- an uncrossed box: the star set is a constrained zonotope, which is a halfspace description
    obtain ⟨P, hP, -⟩ := ConZonotope.exists_construct_eq_iff_hPolytope.mp
      ⟨s.conZonotope, StarSet.conZonotope_exact s hlu⟩
    exact ⟨P, hP⟩
  · -- a crossed box admits no factor, so the star set is empty
    push Not at hlu
    obtain ⟨k, hk⟩ := hlu
    refine ⟨HPolytope.emptySet _, HPolytope.construct_emptySet.trans ?_⟩
    ext x
    refine ⟨fun h => h.elim, fun ⟨α, ⟨hα, _⟩, _⟩ => ?_⟩
    have h : s.dom.inf k ≤ α k ∧ α k ≤ s.dom.sup k := hα k
    linarith [h.1, h.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
