module

public import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
public import CORALean.ContSet.VPolytope.Float.Operations.LinComb
public import CORALean.ContSet.VPolytope.Float.Theorems.NominalLinComb

@[expose] public section

/-!
# `VPolytope.linComb` encloses every segment between the two

Nothing rounds, so there is no spill and `InflatedContSet`'s composition lemma is
not needed: the nominal halves land in the exact `linComb` and the error halves
in the interval one, each by its own layer's theorem.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- the segment splits into a nominal segment and a segment of the two error boxes
theorem VPolytope.linComb_outer (P₁ P₂ : VPolytope (Vec 𝕋 n)) :
    segments P₁.construct P₂.construct ⊆ (P₁.linComb P₂).construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨v₁, hv₁, e₁, he₁, rfl⟩, _, ⟨v₂, hv₂, e₂, he₂, rfl⟩, lam, hlam, rfl⟩
  refine ⟨lam • v₁ + (1 - lam) • v₂, ?_, lam • e₁ + (1 - lam) • e₂, ?_, ?_⟩
  · have h := Real.VPolytope.linComb_outer (nominal P₁) (nominal P₂)
      ⟨v₁, hv₁, v₂, hv₂, lam, hlam, rfl⟩
    rw [← VPolytope.nominal_linComb] at h
    exact h
  · exact Interval.linComb_outer _ _ ⟨e₁, he₁, e₂, he₂, lam, hlam, rfl⟩
  · show lam • v₁ + (1 - lam) • v₂ + (lam • e₁ + (1 - lam) • e₂)
        = lam • (v₁ + e₁) + (1 - lam) • (v₂ + e₂)
    rw [smul_add, smul_add]
    abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
