module

public import CORALean.ContSet.ZonoBundle.Float.Operations.EncloseCora
public import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.SetIntersection.Theorems.PairwiseOuter
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# `ZonoBundle.encloseCora` over-approximates the segments between the operands

The segments between a point of each bundle lie between the points of each pair of members, and
`Zonotope.linComb_outer` puts them in the member `i` of the result (`SetIntersection.pairwise_outer`
at the diagonal pairs). So the union, and with it the convex hull, lies in the result.

## Inputs
* `zB₁` – first bundle
* `zB₂` – second bundle

## Hypotheses
* `h` – the member counts agree

## Conclusion
* the segments between the operands lie in `zB₁.encloseCora zB₂ h`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The segments between the operands lie in the member-wise enclosure. -/
theorem ZonoBundle.encloseCora_outer (zB₁ zB₂ : ZonoBundle (Vec 𝕋 n)) (h : zB₂.k = zB₁.k) :
    Set.linComb zB₁.toSet zB₂.toSet ⊆ (zB₁.encloseCora zB₂ h).toSet :=
  SetIntersection.pairwise_outer Set.linComb
    (fun _ _ _ _ => setLinComb_mono) fun p =>
      ⟨p, Fin.cast h.symm p, Zonotope.linComb_outer _ _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
