import CORALean.ContSet.Conversion.Float.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne

/-!
# A polynomial zonotope as a zonotope, and a constrained one as a constrained
zonotope, over a floating-point scalar

Every dependent factor's monomial lies in `[-1,1]`, so it is read as a free factor
of a zonotope, the dependent generators and then the independent ones; the error
box is carried across. Nothing rounds, and the exponents are dropped, which is
what makes this an enclosure rather than the set.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The dependent generators, then the independent ones, side by side. -/
def PolyZonotope.zonotope (pZ : PolyZonotope 𝕋 n) : Zonotope 𝕋 n where
  h := pZ.h + pZ.q
  c := pZ.c
  G := fun i => Fin.append (pZ.G i) (pZ.GI i)
  E := pZ.err

def PolyZonotope.conZonotope (pZ : PolyZonotope 𝕋 n) : ConZonotope 𝕋 n :=
  pZ.zonotope.conZonotope

def ConPolyZono.conZonotope (cPZ : ConPolyZono 𝕋 n) : ConZonotope 𝕋 n :=
  cPZ.polyZonotope.conZonotope

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.zonotope_contains (pZ : PolyZonotope 𝕋 n) :
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
      toReal (Fin.append (pZ.G i) (pZ.GI i) l) * _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    ring

theorem PolyZonotope.conZonotope_contains (pZ : PolyZonotope 𝕋 n) :
    pZ.construct ⊆ pZ.conZonotope.construct :=
  subset_trans pZ.zonotope_contains pZ.zonotope.conZonotope_contains

theorem ConPolyZono.conZonotope_contains (cPZ : ConPolyZono 𝕋 n) :
    cPZ.construct ⊆ cPZ.conZonotope.construct :=
  subset_trans cPZ.polyZonotope_contains cPZ.polyZonotope.conZonotope_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
