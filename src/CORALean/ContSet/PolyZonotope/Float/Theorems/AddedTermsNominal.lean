module

public import CORALean.ContSet.PolyZonotope.Float.Operations.AddedTerms
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.AddedTerms

@[expose] public section

/-!
# The float `addedTerms` denotes the exact one

The float `addedTerms` copies the stored floats, so its exponents are the exact layer's `addedTerms`
exponents of the nominal set and its generator `idx` reads as the exact one; the error box is the
point `0`. (The float set is a vector of length `1`, the exact one a scalar one.)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.addedTerms_nominal (pZ : PolyZonotope (Vec 𝕋 n)) :
    (∀ idx, toReal (pZ.addedTerms.G idx 0)
      = (Real.PolyZonotope.addedTerms (PolyZonotope.nominal pZ)).G idx)
    ∧ pZ.addedTerms.E = (Real.PolyZonotope.addedTerms (PolyZonotope.nominal pZ)).E
    ∧ pZ.addedTerms.err = Interval.point fun _ => zero := by -- --- PROOF ---
  refine ⟨fun idx => ?_, rfl, rfl⟩
  simp only [PolyZonotope.addedTerms, Real.PolyZonotope.addedTerms]
  generalize finProdFinEquiv.symm idx = pr
  obtain ⟨i, g⟩ := pr
  refine Fin.cases ?_ (fun g' => ?_) g <;> rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
