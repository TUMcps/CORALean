module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalOn
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapPoint

@[expose] public section

/-!
# `map` carries the evaluation along with it

`map` touches neither the factor count nor the exponent matrix, so one factor
vector reads both sides, and it sends the independent block through `f` as
well — hence an *equality* and not an enclosure. This is [1, Def. 4] at a linear
map: the property that makes it dependency preserving, discharged rather than
assumed as [1]'s Sec. 2.3 does.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One evaluated point moved by `f`, the independent block included. -/
theorem PolyZonotope.aux_map_eval (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ)
    (γ : Fin pZ.q → ℝ) :
    (pZ.map f).point a + ∑ j, γ j • (pZ.map f).GI j
      = f (pZ.point a + ∑ j, γ j • pZ.GI j) := by
  show (pZ.map f).point a + ∑ j, γ j • f (pZ.GI j) = _
  rw [PolyZonotope.map_point, map_add, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => (map_smul f _ (pZ.GI j)).symm)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `map`'s evaluation at `B` is `f`'s image of the original's. -/
theorem PolyZonotope.map_evalOn (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α)
    (B : Set (Fin pZ.p → ℝ)) : (pZ.map f).evalOn B = f '' pZ.evalOn B := by -- --- PROOF ---
  ext x
  constructor
  · -- forwards: the same factors and the same coefficients name the preimage
    rintro ⟨a, ha, γ, hγ, rfl⟩
    exact ⟨_, ⟨a, ha, γ, hγ, rfl⟩, (PolyZonotope.aux_map_eval f pZ a γ).symm⟩
  · rintro ⟨_, ⟨a, ha, γ, hγ, rfl⟩, rfl⟩
    exact ⟨a, ha, γ, hγ, (PolyZonotope.aux_map_eval f pZ a γ).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
