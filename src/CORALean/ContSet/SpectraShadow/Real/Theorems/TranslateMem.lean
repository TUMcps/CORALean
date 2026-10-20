module

public import CORALean.ContSet.SpectraShadow.Real.Operations.Basic

@[expose] public section

/-!
# A translated shadow is the shifted set

`x` is in `S.translate v` exactly when `x - v` is in `S`: the same inequality, the point moved by
`v`. Exact.

## Inputs
* `S` – spectrahedral shadow
* `v` – point
* `x` – point

## Hypotheses
* none

## Conclusion
* A translated shadow is the shifted set
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.mem_translate_iff (S : SpectraShadow α) (v x : α) :
    x ∈ (S.translate v).construct ↔ x - v ∈ S.construct := by -- --- PROOF ---
  constructor
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨β, hβ, ?_⟩
    change S.c + v + ∑ i : Fin S.m, β i • S.G i - v = S.c + ∑ i : Fin S.m, β i • S.G i
    abel
  · rintro ⟨β, hβ, h⟩
    refine ⟨β, hβ, ?_⟩
    rw [sub_eq_iff_eq_add] at h
    change x = S.c + v + ∑ i : Fin S.m, β i • S.G i
    rw [h]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
