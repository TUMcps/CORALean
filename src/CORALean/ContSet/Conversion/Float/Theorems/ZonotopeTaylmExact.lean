module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import Mathlib.Algebra.BigOperators.Pi
public import CORALean.ContSet.Conversion.Float.Operations.Basic

@[expose] public section

/-!
# A zonotope as an array of Taylor models, over a floating-point scalar

CORA's `taylm(zonotope)`: one variable per generator, `c + G t` over `t ∈ [-1, 1]ʰ`. The
stored floats are the model's coefficients unchanged, so nothing rounds, and the
zonotope's error box becomes each coordinate's error box, the remainder `[0, 0]`. Exact, as over
ℝ.

## Inputs
* `Z` – zonotope
* `N` – Taylor order

## Hypotheses
* none

## Conclusion
* Taylor model equals the zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Zonotope.aux_taylm_poly (Z : Zonotope (Vec 𝕋 n)) (N : ℕ) (i : Fin n)
    (t : Vec ℝ Z.h) :
    (Z.taylm N i).inflated.poly t = toReal (Z.c i) + ∑ j, toReal (Z.G j i) * t j := by
  simp only [Zonotope.taylm, Taylm.inflated, Real.Taylm.poly, List.map_cons, List.map_ofFn,
    Real.Taylm.polyOf_cons, Real.Taylm.polyOf_ofFn, Real.Taylm.monomial_zero,
    Function.comp_def, Real.Taylm.monomial_single, mul_one]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.taylm_exact (Z : Zonotope (Vec 𝕋 n)) (N : ℕ) : -- --- CONCL ---
    Taylm.construct (Z.taylm N) = Z.construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    have hp : (fun i => toReal (Z.c i) + ∑ j, toReal (Z.G j i) * t j)
        ∈ InflatedContSet.nominalSet Z :=
      Zonotope.mem_nominalSet_iff.mpr ⟨t, ht, fun i => rfl⟩
    refine ⟨_, hp, x - fun i => toReal (Z.c i) + ∑ j, toReal (Z.G j i) * t j, fun i => ?_, ?_⟩
    · have h : toReal zero + toReal (Z.I_error.inf i) ≤ x i - (Z.taylm N i).inflated.poly t ∧
          x i - (Z.taylm N i).inflated.poly t ≤ toReal zero + toReal (Z.I_error.sup i) := hx i
      rw [Zonotope.aux_taylm_poly, toReal_zero, zero_add, zero_add] at h
      exact h
    · show (_ : Vec ℝ n) + (x - _) = x
      exact add_sub_cancel _ _
  -- a point of the zonotope plus its error: the coefficients are the variables
  · rintro ⟨p, hp, e, he, rfl⟩
    obtain ⟨β, hβ, hpβ⟩ := Zonotope.mem_nominalSet_iff.mp hp
    refine ⟨β, hβ, fun i => ?_⟩
    have h2 : toReal (Z.I_error.inf i) ≤ e i ∧ e i ≤ toReal (Z.I_error.sup i) := he i
    show toReal zero + toReal (Z.I_error.inf i) ≤ (p + e) i - (Z.taylm N i).inflated.poly β ∧
      (p + e) i - (Z.taylm N i).inflated.poly β ≤ toReal zero + toReal (Z.I_error.sup i)
    rw [Zonotope.aux_taylm_poly, toReal_zero, zero_add, zero_add, Pi.add_apply, hpβ i]
    constructor <;> linarith [h2.1, h2.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
