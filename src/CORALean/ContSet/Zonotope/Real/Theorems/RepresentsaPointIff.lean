module

public import CORALean.ContSet.Zonotope.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import Mathlib.Algebra.Module.BigOperators

@[expose] public section

/-!
# A zonotope is a point iff every generator vanishes

If `c + Gⱼ` (the coefficient `βⱼ = 1`, the others `0`) lies in `{c}` then `Gⱼ = 0`; conversely
with no generator the combination is `0`. The origin is the point whose center is `0`. The empty
set is never represented: `Zonotope.center_mem_construct` puts the center in every zonotope.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* `Z` is its center iff `representsa_point` holds
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.representsa_point_iff (Z : Zonotope α) : -- --- CONCL ---
    Z.construct = {Z.c} ↔ Z.representsa_point := by -- --- PROOF ---
  constructor
  · intro h j
    have hmem : Z.c + Z.G j ∈ Z.construct :=
      ⟨Pi.single j 1, fun i => by
        by_cases hij : i = j <;> simp [hij], by simp⟩
    rw [h] at hmem
    exact add_eq_left.mp hmem
  · intro h
    ext x
    constructor
    · rintro ⟨β, -, rfl⟩
      simp [h _]
    · rintro rfl
      exact Zonotope.center_mem_construct Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
