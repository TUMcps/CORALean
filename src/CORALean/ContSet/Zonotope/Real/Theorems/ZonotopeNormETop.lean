module

public import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm

@[expose] public section

/-!
# The extended zonotope norm is `Inf` off the range of the generators

`Zonotope.zonotopeNormE` is `⊤` for a point no coefficient vector reaches: the minimum over the
empty set, which CORA returns as `Inf`.

## Inputs
* `Z` – zonotope
* `p` – point

## Hypotheses
* `hp` – no coefficient vector reaches the point

## Conclusion
* `zonotopeNormE` is `⊤`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       03-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The extended norm is `⊤` where no coefficient vector reaches the point: the minimum over
nothing. -/
theorem Zonotope.zonotopeNormE_eq_top (Z : Zonotope α) {p : α} (hp : ¬∃ γ, Z.genMap γ = p) :
    Z.zonotopeNormE p = ⊤ := by
  have : {γ | Z.genMap γ = p} = ∅ := Set.eq_empty_of_forall_notMem fun γ hγ => hp ⟨γ, hγ⟩
  simp [Zonotope.zonotopeNormE, this]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
