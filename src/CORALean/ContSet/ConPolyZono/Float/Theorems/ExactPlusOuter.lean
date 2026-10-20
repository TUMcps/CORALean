module

public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.ConPolyZono.Float.Operations.ExactPlus
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Real.Operations.ExactPlus
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemRelaxVecIff
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEqUnit

@[expose] public section

/-!
# `ConPolyZono.exactPlus` encloses the exact one at the nominal sets

The exact layer's `exactPlus` of what the two sets' stored floats describe (`nominalCore`), its
rows relaxed by the first set's slack, plus both error boxes, lies in the float `exactPlus`. A
point of the exact one is the two nominal points at one common factor value meeting the first
set's constraints within their slack; the float one reads the same blocks and the
same constraints at the same factors and coefficients, and differs only by the rounding of the
center sum, which its error box holds. Outer only: never the exact `exactPlus` at float.

## Inputs
* `cPZ₁` – first summand
* `cPZ₂` – second summand

## Hypotheses
* `hp` – both have the same number of factors

## Conclusion
* the exact sum of the nominal parts is contained in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem ConPolyZono.aux_exactPlus_nominal (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (hp : cPZ₁.p = cPZ₂.p) : -- --- CONCL ---
    ((Real.ConPolyZono.exactPlus cPZ₁.nominalCore cPZ₂.nominalCore hp).relax
        (toRealVec cPZ₁.cons.b_error)).construct
      ⊆ nominalSet (cPZ₁.exactPlus cPZ₂ hp)
        + (PolyZonotope.centerResidual cPZ₁.c cPZ₂.c).construct := by -- --- PROOF ---
  intro y hy
  obtain ⟨a, β, ha, hβ, hs, hy⟩ := (Real.ConPolyZono.mem_relax_vec_iff _ _).mp hy
  -- the float point at the same factors and coefficients, off by the center's rounding
  refine ⟨fun i => toReal ((cPZ₁.exactPlus cPZ₂ hp).c i)
            + (∑ l, toReal ((cPZ₁.exactPlus cPZ₂ hp).G l i)
                * Real.PolyZonotope.monomial (cPZ₁.exactPlus cPZ₂ hp).E a l)
            + ∑ j, toReal ((cPZ₁.exactPlus cPZ₂ hp).GI j i) * β j,
          ConPolyZono.mem_nominalSet_iff.mpr
            ⟨a, β, ha, hβ,
              (PolyLevelSet.mem_construct_iff_of_eq_unit cPZ₁.cons_eq cPZ₁.cons_dom).mpr ⟨ha, hs⟩,
                fun _ => rfl⟩,
          fun i => toReal (cPZ₁.c i) + toReal (cPZ₂.c i)
            - toReal ((cPZ₁.exactPlus cPZ₂ hp).c i),
          Interval.sub_mem_residual fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩, ?_⟩
  funext i
  -- the stored blocks read back as the exact layer's appended ones, entry by entry
  have hG : ∀ l : Fin (cPZ₁.h + cPZ₂.h), toReal (Fin.append cPZ₁.G cPZ₂.G l i)
      = Fin.append cPZ₁.nominalCore.G cPZ₂.nominalCore.G l i :=
    Fin.addCases
      (fun l => by
        rw [Fin.append_left]
        exact (congrFun (Fin.append_left cPZ₁.nominalCore.G cPZ₂.nominalCore.G l) i).symm)
      fun l => by
        rw [Fin.append_right]
        exact (congrFun (Fin.append_right cPZ₁.nominalCore.G cPZ₂.nominalCore.G l) i).symm
  -- the independent blocks likewise
  have hGI : ∀ j : Fin (cPZ₁.qI + cPZ₂.qI), toReal (Fin.append cPZ₁.GI cPZ₂.GI j i)
      = Fin.append cPZ₁.nominalCore.GI cPZ₂.nominalCore.GI j i :=
    Fin.addCases
      (fun j => by
        rw [Fin.append_left]
        exact (congrFun (Fin.append_left cPZ₁.nominalCore.GI cPZ₂.nominalCore.GI j) i).symm)
      fun j => by
        rw [Fin.append_right]
        exact (congrFun (Fin.append_right cPZ₁.nominalCore.GI cPZ₂.nominalCore.GI j) i).symm
  rw [hy i]
  simp only [Pi.add_apply, Real.ConPolyZono.exactPlus, Real.PolyZonotope.exactPlus,
    ConPolyZono.exactPlus, PolyZonotope.exactPlus, ConPolyZono.toPolyZonotope, hG, hGI]
  -- the two exponent matrices agree only up to unfolding `nominal`, so match by defeq
  have key : ∀ d A B c₁ c₂ : ℝ, d + A + B + (c₁ + c₂ - d) = c₁ + c₂ + A + B :=
    fun _ _ _ _ _ => by ring
  exact key _ _ _ _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.exactPlus_outer (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (hp : cPZ₁.p = cPZ₂.p) : -- --- CONCL ---
    ((Real.ConPolyZono.exactPlus cPZ₁.nominalCore cPZ₂.nominalCore hp).relax
        (toRealVec cPZ₁.cons.b_error)).construct + (cPZ₁.I_error.construct + cPZ₂.I_error.construct)
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
