import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.ConPolyZono.Float.Operations.ExactPlus
import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
import CORALean.ContSet.ConPolyZono.Real.Operations.ExactPlus
import CORALean.ContSet.ConPolyZono.Real.Theorems.MemConstruct

/-!
# `ConPolyZono.exactPlus` encloses the exact one at the nominal sets

The exact layer's `exactPlus` of what the two sets' stored floats denote, plus both error boxes,
lies in the float `exactPlus`. A point of the exact one is the two nominal points at one common
factor value meeting the first set's constraints; the float one reads the same blocks and the
same constraints at the same factors and coefficients, and differs only by the rounding of the
centre sum, which its error box holds. Outer only: never the exact `exactPlus` at float.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem ConPolyZono.aux_exactPlus_nominal (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (hp : cPZ₁.p = cPZ₂.p) :
    (Real.ConPolyZono.exactPlus (nominal cPZ₁) (nominal cPZ₂) hp).construct
      ⊆ nominalSet (cPZ₁.exactPlus cPZ₂ hp)
        + (PolyZonotope.centerResidual cPZ₁.c cPZ₂.c).construct := by -- --- PROOF ---
  intro y hy
  obtain ⟨a, β, ha, hβ, hs, hy⟩ := Real.ConPolyZono.mem_construct_iff.mp hy
  -- the float point at the same factors and coefficients, off by the centre's rounding
  refine ⟨fun i => toReal ((cPZ₁.exactPlus cPZ₂ hp).c i)
            + (∑ l, toReal ((cPZ₁.exactPlus cPZ₂ hp).G l i)
                * Real.PolyZonotope.monomial (cPZ₁.exactPlus cPZ₂ hp).E a l)
            + ∑ j, toReal ((cPZ₁.exactPlus cPZ₂ hp).GI j i) * β j,
          ConPolyZono.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, hs, fun _ => rfl⟩,
          fun i => toReal (cPZ₁.c i) + toReal (cPZ₂.c i)
            - toReal ((cPZ₁.exactPlus cPZ₂ hp).c i),
          Interval.sub_mem_residual fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩, ?_⟩
  funext i
  -- the stored blocks read back as the exact layer's appended ones, entry by entry
  have hG : ∀ l : Fin (cPZ₁.h + cPZ₂.h), toReal (Fin.append cPZ₁.G cPZ₂.G l i)
      = Fin.append (nominal cPZ₁).G (nominal cPZ₂).G l i :=
    Fin.addCases
      (fun l => by
        rw [Fin.append_left]
        exact (congrFun (Fin.append_left (nominal cPZ₁).G (nominal cPZ₂).G l) i).symm)
      fun l => by
        rw [Fin.append_right]
        exact (congrFun (Fin.append_right (nominal cPZ₁).G (nominal cPZ₂).G l) i).symm
  -- the independent blocks likewise
  have hGI : ∀ j : Fin (cPZ₁.q + cPZ₂.q), toReal (Fin.append cPZ₁.GI cPZ₂.GI j i)
      = Fin.append (nominal cPZ₁).GI (nominal cPZ₂).GI j i :=
    Fin.addCases
      (fun j => by
        rw [Fin.append_left]
        exact (congrFun (Fin.append_left (nominal cPZ₁).GI (nominal cPZ₂).GI j) i).symm)
      fun j => by
        rw [Fin.append_right]
        exact (congrFun (Fin.append_right (nominal cPZ₁).GI (nominal cPZ₂).GI j) i).symm
  rw [hy i]
  simp only [Pi.add_apply, Real.ConPolyZono.exactPlus, Real.PolyZonotope.exactPlus,
    ConPolyZono.exactPlus, PolyZonotope.exactPlus, ConPolyZono.toPolyZonotope, hG, hGI]
  -- the two exponent matrices agree only up to unfolding `nominal`, so match by defeq
  have key : ∀ d A B c₁ c₂ : ℝ, d + A + B + (c₁ + c₂ - d) = c₁ + c₂ + A + B :=
    fun _ _ _ _ _ => by ring
  exact key _ _ _ _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.exactPlus_outer (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) (hp : cPZ₁.p = cPZ₂.p) :
    (Real.ConPolyZono.exactPlus (nominal cPZ₁) (nominal cPZ₂) hp).construct
        + (cPZ₁.err.construct + cPZ₂.err.construct)
      ⊆ (cPZ₁.exactPlus cPZ₂ hp).construct := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨y', hy', r, hr, hyr⟩ := ConPolyZono.aux_exactPlus_nominal cPZ₁ cPZ₂ hp hy
  refine ⟨y', hy', e + r, Interval.plus_outer _ _ ⟨e, Interval.plus_outer _ _ he, r, hr, rfl⟩, ?_⟩
  have hyr' : y' + r = y := hyr
  show y' + (e + r) = y + e
  rw [← hyr']
  abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
