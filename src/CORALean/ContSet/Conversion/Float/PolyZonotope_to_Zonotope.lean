import CORALean.ContSet.Conversion.Float.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

/-!
# A polynomial zonotope as a zonotope, over a floating-point scalar

Every dependent factor's monomial lies in `[-1,1]`, so it is read as a free factor
of a zonotope, the dependent generators and then the independent ones; the error
box is carried across. Nothing rounds, and the exponents are dropped, which is
what makes this an enclosure rather than the set. A constrained polynomial
zonotope goes through its polynomial zonotope, as over ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The dependent generators, then the independent ones, side by side. -/
def PolyZonotope.zonotope (pZ : PolyZonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := pZ.h + pZ.q
  c := pZ.c
  G := Fin.append pZ.G pZ.GI
  E := pZ.err

def ConPolyZono.zonotope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  cPZ.polyZonotope.zonotope

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.zonotope_contains (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.zonotope.construct := by -- --- PROOF ---
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  refine Zonotope.mem_nominalSet_iff.mpr
    ⟨Fin.append (Real.PolyZonotope.monomial pZ.E a) β, ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) fun j => ?_
    · simpa using Real.PolyZonotope.abs_monomial_le_one pZ.E ha l
    · simpa using hβ j
  · rw [hx i]
    show _ = toReal (pZ.c i) + ∑ l : Fin (pZ.h + pZ.q),
      toReal (Fin.append pZ.G pZ.GI l i) * _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    ring

theorem ConPolyZono.zonotope_contains (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.zonotope.construct :=
  subset_trans cPZ.polyZonotope_contains cPZ.polyZonotope.zonotope_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
