import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

/-!
# A zonotope as a polynomial zonotope, over a floating-point scalar

Nothing rounds. The generators are copied, each factor gets the exponent matrix's
identity column so every monomial is the factor itself, and the error box is
carried across.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def Zonotope.polyZonotope (Z : Zonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := Z.h
  h := Z.h
  q := 0
  c := Z.c
  G := Z.G
  E := Real.PolyZonotope.identE Z.h
  GI := Fin.elim0
  err := Z.E

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.polyZonotope_contains (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ Z.polyZonotope.construct := by -- --- PROOF ---
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp hx
  -- identity exponents make every monomial a factor
  refine PolyZonotope.mem_nominalSet_iff.mpr ⟨β, fun j => j.elim0, hβ, fun j => j.elim0,
    fun i => ?_⟩
  rw [hx i]
  simp only [Zonotope.polyZonotope, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Real.PolyZonotope.monomial_identE]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
