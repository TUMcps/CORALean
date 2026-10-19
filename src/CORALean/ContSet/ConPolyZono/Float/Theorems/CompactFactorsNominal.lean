module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactFactorsEqSpec
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Real.Operations.AbsFactorExtendLeOne
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorExtendLeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorExtendRight
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxLeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxRight
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# `compactFactors` leaves the nominal part as it was

Costs nothing at all: it changes `p` and both exponent matrices, all over ℕ, and every monomial
it keeps reads the same kept factors (`monomial_factorIdx_left`, `monomial_factorIdx_right`), a
dropped factor coming back as `0` (`factorExtend`), as in the exact layer's `compactFactors_exact`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.compactFactors_nominal (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    nominalSet cPZ = nominalSet cPZ.compactFactors := by -- --- PROOF ---
  rw [ConPolyZono.compactFactors_eq_spec]
  ext x
  rw [ConPolyZono.mem_nominalSet_iff, ConPolyZono.mem_nominalSet_iff]
  constructor
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    have hR : Real.PolyZonotope.monomial cPZ.compactFactorsSpec.cons.R
        (fun k => a (Real.ConPolyZono.factorIdx cPZ.E cPZ.cons.R k))
        = Real.PolyZonotope.monomial cPZ.cons.R a :=
      funext fun l => Real.ConPolyZono.monomial_factorIdx_right cPZ.E cPZ.cons.R a l
    refine ⟨fun k => a (Real.ConPolyZono.factorIdx cPZ.E cPZ.cons.R k), β, fun k => ha _, hβ,
      (PolyLevelSet.mem_construct_iff_of_eq cPZ.compactFactorsSpec.cons_eq).mpr fun i => ?_,
      fun i => ?_⟩
    -- a row of the kept factors reads what the row of all of them read
    · have h := (PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq).mp hs i
      rw [← hR] at h
      exact h
    · rw [hx i]
      show _ = toReal (cPZ.c i) + (∑ l, toReal (cPZ.G l i) * Real.PolyZonotope.monomial
          (fun k i => cPZ.E (Real.ConPolyZono.factorIdx cPZ.E cPZ.cons.R k) i)
          (fun k => a (Real.ConPolyZono.factorIdx cPZ.E cPZ.cons.R k)) l) + _
      simp only [Real.ConPolyZono.monomial_factorIdx_left]
      rfl
  -- back: a dropped factor returns as `0`, which no monomial reads
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    have hR : Real.PolyZonotope.monomial cPZ.cons.R
        (Real.ConPolyZono.factorExtend cPZ.E cPZ.cons.R a)
        = Real.PolyZonotope.monomial cPZ.compactFactorsSpec.cons.R a :=
      funext fun l => Real.ConPolyZono.monomial_factorExtend_right cPZ.E cPZ.cons.R a l
    refine ⟨Real.ConPolyZono.factorExtend cPZ.E cPZ.cons.R a, β,
      fun k => Real.ConPolyZono.abs_factorExtend_le_one cPZ.E cPZ.cons.R ha k, hβ,
      (PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq).mpr fun i => ?_, fun i => ?_⟩
    · have h := (PolyLevelSet.mem_construct_iff_of_eq cPZ.compactFactorsSpec.cons_eq).mp hs i
      rw [← hR] at h
      exact h
    · rw [hx i]
      show toReal (cPZ.c i) + (∑ l, toReal (cPZ.G l i) * Real.PolyZonotope.monomial
          (fun k i => cPZ.E (Real.ConPolyZono.factorIdx cPZ.E cPZ.cons.R k) i) a l) + _ = _
      simp only [Real.ConPolyZono.monomial_factorExtend_left]
      rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
