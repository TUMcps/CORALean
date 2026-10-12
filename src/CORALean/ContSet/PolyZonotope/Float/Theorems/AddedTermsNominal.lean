import CORALean.ContSet.PolyZonotope.Float.Operations.AddedTerms
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.AddedTerms

/-!
# The float `addedTerms` denotes the exact one

The float `addedTerms` copies the stored floats, so its exponents are the exact layer's `addedTerms`
exponents of the nominal set and its generator `idx` reads as the exact one; the error box is the
point `0`. (The float set is a vector of length `1`, the exact one a scalar one.)
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.addedTerms_nominal (pZ : PolyZonotope 𝕋 n) :
    (∀ idx, toReal (pZ.addedTerms.G idx 0)
      = (Real.PolyZonotope.addedTerms (GPolyZonotope.nominal pZ)).G idx)
    ∧ pZ.addedTerms.E = (Real.PolyZonotope.addedTerms (GPolyZonotope.nominal pZ)).E
    ∧ pZ.addedTerms.err = Interval.point fun _ => zero := by -- --- PROOF ---
  refine ⟨fun idx => ?_, rfl, rfl⟩
  simp only [PolyZonotope.addedTerms, Real.PolyZonotope.addedTerms]
  generalize finProdFinEquiv.symm idx = pr
  obtain ⟨i, g⟩ := pr
  refine Fin.cases ?_ (fun g' => ?_) g <;> rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
