import CORALean.ContSet.PolyZonotope.Float.Theorems.BilinGClose
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct

/-!
# `PolyZonotope.bilin` contains the exact pairing of its operands' nominal parts

The two representations differ in their generator entries alone, and `generatorError` prices that
difference exactly as it does for `mtimes` and `quadMap`: the stored generators, rounded down,
are within `bilinGDiff` of the exact ones (`bilinG_close`), so the exact pairing's point at any
factors is the stored point plus a member of the error box. Outer only.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exact pairing of the nominal parts lies in the float pairing: the stored generators differ
from the exact ones inside the error box. -/
theorem PolyZonotope.bilin_refines (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n))
    (hp : pZ₁.p = pZ₂.p) :
    (Real.PolyZonotope.bilin (Real.PolyZonotope.quadBilin fun k => toRealMat (Q k))
        (nominal pZ₁) (nominal pZ₂) hp).construct
      ⊆ (PolyZonotope.bilin Q pZ₁ pZ₂ hp).construct := by -- --- PROOF ---
  intro x hx
  -- a point of the exact pairing: factors `a`, coefficients `b`
  obtain ⟨a, b, ha, hb, hx⟩ := Real.PolyZonotope.mem_construct_iff.mp hx
  -- the stored generators' rounding against each monomial lies in the error box
  have hbox : (fun i => ∑ l,
        (Real.PolyZonotope.bilinG (Real.PolyZonotope.quadBilin fun k => toRealMat (Q k))
            (nominal pZ₁) (nominal pZ₂) l i
          - toReal (PolyZonotope.bilinGDown Q pZ₁ pZ₂ i l))
            * Real.PolyZonotope.monomial (PolyZonotope.bilinE pZ₁ pZ₂ hp) a l)
      ∈ (PolyZonotope.generatorError (PolyZonotope.bilinGDiff Q pZ₁ pZ₂)).construct :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.bilinG_close Q pZ₁ pZ₂) ha
  -- the nominal point of the float pairing at the same factors, then the box's share
  refine ⟨fun i => toReal ((PolyZonotope.bilin Q pZ₁ pZ₂ hp).c i)
            + (∑ l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1)),
                toReal (PolyZonotope.bilinGDown Q pZ₁ pZ₂ i l)
                * Real.PolyZonotope.monomial (PolyZonotope.bilinE pZ₁ pZ₂ hp) a l)
            + ∑ j : Fin 0, toReal ((PolyZonotope.bilin Q pZ₁ pZ₂ hp).GI j i) * b j,
          PolyZonotope.mem_nominalSet_iff.mpr ⟨a, b, ha, hb, fun _ => rfl⟩, _, hbox, ?_⟩
  funext i
  -- stored generators plus their rounding are the exact ones, monomial by monomial
  have hsum : (∑ l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1)),
          toReal (PolyZonotope.bilinGDown Q pZ₁ pZ₂ i l)
        * Real.PolyZonotope.monomial (PolyZonotope.bilinE pZ₁ pZ₂ hp) a l)
      + (∑ l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1)),
          (Real.PolyZonotope.bilinG (Real.PolyZonotope.quadBilin fun k => toRealMat (Q k))
              (nominal pZ₁) (nominal pZ₂) l i
            - toReal (PolyZonotope.bilinGDown Q pZ₁ pZ₂ i l))
              * Real.PolyZonotope.monomial (PolyZonotope.bilinE pZ₁ pZ₂ hp) a l)
      = ∑ l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1)),
          Real.PolyZonotope.bilinG (Real.PolyZonotope.quadBilin fun k => toRealMat (Q k))
              (nominal pZ₁) (nominal pZ₂) l i
            * Real.PolyZonotope.monomial (PolyZonotope.bilinE pZ₁ pZ₂ hp) a l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  -- unfold both sides to their sums over the generators
  simp only [Pi.add_apply, PolyZonotope.bilin, toReal_zero, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero, zero_add]
  rw [hx i]
  simp only [Real.PolyZonotope.bilin, Pi.zero_apply,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]
  exact hsum

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
