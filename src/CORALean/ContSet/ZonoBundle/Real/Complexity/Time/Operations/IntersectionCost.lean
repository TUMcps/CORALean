module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Intersection
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ZonoBundle.intersectionCost`

Asserted, not proved, and no longer zero: `Operations/Intersection.lean` concatenates the two
families of members and computes nothing at all. The result is a new family all the same, and
every entry of each member is a write.

This is still what the representation is for: an intersection a zonotope cannot represent costs a
bundle no arithmetic to *take* — the members are kept side by side and the set they denote is
their intersection by definition. What it costs beyond the copy is paid later and elsewhere, in
the `k₁ + k₂` members every subsequent operation then runs over, which is exactly what `plusCost`
and `mtimesCost` charge for.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.intersection` costs at `Vec ℝ n` on bundles of `k₁` and `k₂` members, none
over `h₁` and `h₂` generators: one write for each of the `n * (hᵢ + 1)` entries of every member of
both. -/
def ZonoBundle.intersectionCost (n k₁ k₂ h₁ h₂ : ℕ) : Cost :=
  ⟨k₁ * (n * (h₁ + 1)) + k₂ * (n * (h₂ + 1))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
