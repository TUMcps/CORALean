module

public import CORALean.ContSet.ConPolyZono.Float.Operations.GetSubset
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemGetSubsetOfReal
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemRelaxVecIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetGClose
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial

@[expose] public section

/-!
# `ConPolyZono.getSubset` over-approximates the exact re-parametrization

A point of the exact layer's `getSubset` of the stored set (`nominalCore`), its rows relaxed by the
stored slack, plus a point of its error box, is a point of the float `getSubset`. The generators
are as for `PolyZonotope.getSubset`: the rounding they cost, scaled by monomials in `[-1, 1]`,
lies in the box added to `err`. The constraint matrix
is rounded the same way, and the same bound, scaled by the same monomials, moves the exact
constraint value into the widened slack: what `A μ` loses to the rounding of `A` is at most the
row radius the slack was widened by, so the stored system holds wherever the exact one does.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `k` – factor index
* `cen` – center of the subinterval
* `rad` – radius of the subinterval

## Hypotheses
* none

## Conclusion
* the exact re-parametrization is contained in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.getSubset_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (k : Fin cPZ.p)
    (cen rad : 𝕋) : -- --- CONCL ---
    ((Real.ConPolyZono.getSubset cPZ.nominalCore k (toReal cen) (toReal rad)).relax
        (toRealVec cPZ.cons.b_error)).construct + cPZ.I_error.construct
      ⊆ (cPZ.getSubset k cen rad).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hsat, hz⟩ := (Real.ConPolyZono.mem_relax_vec_iff _ _).mp hz
  -- the exact generators, the stored (rounded down) ones and the monomials, named once
  set G := Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen) (toReal rad)
  set Gd : Fin n → Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)) → 𝕋 :=
    cPZ.toPolyZonotope.getSubsetGDown k cen rad
  set mon := Real.PolyZonotope.monomial
    (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a
  -- the generator error of the subset's difference of generators
  set GE := PolyZonotope.generatorError (cPZ.toPolyZonotope.getSubsetGDiff k cen rad) with hGE
  -- the rounding of the generators, scaled by the monomials, lies in the added box
  set err : Fin n → ℝ := fun i => ∑ l : Fin (cPZ.toPolyZonotope.h *
    (cPZ.toPolyZonotope.maxExp k + 1)), (G l i - toReal (Gd i l)) * mon l with herr
  have hbox : err ∈
      GE.construct :=
    PolyZonotope.mem_generatorError_monomial
      (PolyZonotope.getSubsetG_close cPZ.toPolyZonotope k cen rad) ha
  -- the float point at the same factors and coefficients, plus what the rounding and the box add
  refine ⟨fun i => toReal ((cPZ.getSubset k cen rad).c i)
      + (∑ l, toReal ((cPZ.getSubset k cen rad).G l i)
          * Real.PolyZonotope.monomial (cPZ.getSubset k cen rad).E a l)
      + ∑ j : Fin cPZ.qI, toReal ((cPZ.getSubset k cen rad).GI j i) * β j,
    ConPolyZono.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ,
      PolyLevelSet.mem_getSubset_of_real cPZ.cons cPZ.cons_eq k cen rad a ha
        (cPZ.cons_dom ▸ (Interval.mem_unit_iff a).mpr ha) hsat, fun _ => rfl⟩,
    fun i => err i + e i,
    ?_, ?_⟩
  · -- the sum of the two boxes' points is a point of the interval sum
    intro i
    have h₁ : toReal (cPZ.toPolyZonotope.I_error.inf i) ≤ e i := (he i).1
    have h₂ : e i ≤ toReal (cPZ.toPolyZonotope.I_error.sup i) := (he i).2
    -- the generator rounding's point, within its own box
    have h₃ : toReal (GE.inf i) ≤ err i ∧
        err i ≤ toReal (GE.sup i) := hbox i
    refine ⟨le_trans (addDown_le_add _ _) ?_, le_trans ?_ (add_le_addUp _ _)⟩
    · simp only [Entrywise.entry]
      linarith [h₃.1]
    · simp only [Entrywise.entry]
      linarith [h₃.2]
  · funext i
    -- the exact point's coordinate, with the stored fields spelt as the exact ones
    have hzi : z i = toReal (cPZ.c i)
        + (∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)), G l i * mon l)
        + ∑ j : Fin cPZ.qI, toReal (cPZ.GI j i) * β j := hz i
    -- the stored and the exact generator sums differ by exactly the box's point
    have hsum : (∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          toReal (Gd i l) * mon l) + err i
        = ∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)), G l i * mon l := by
      simp only [herr]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    -- spelt out, the coordinate is the exact point's plus the box's
    show toReal (cPZ.c i) + (∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          toReal (Gd i l) * mon l)
        + (∑ j : Fin cPZ.qI, toReal (cPZ.GI j i) * β j) + (err i + e i) = z i + e i
    rw [hzi]
    linarith [hsum]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
