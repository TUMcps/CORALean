module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# A zonotope as an array of Taylor models, over a floating-point scalar

CORA's `taylm(zonotope)`: one variable per generator, `c + G t` over `t ∈ [-1, 1]ʰ`. The
stored floats are the model's coefficients unchanged, so nothing rounds, and the
zonotope's error box becomes each coordinate's remainder. Exact, as over ℝ.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def Zonotope.taylm (Z : Zonotope (Vec 𝕋 n)) (N : ℕ) : Fin n → Taylm 𝕋 Z.h :=
  fun i => ⟨(Z.c i, 0) :: List.ofFn (fun j => (Z.G j i, Pi.single j 1)),
    Z.I_error.inf i, Z.I_error.sup i, N⟩

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Zonotope.aux_taylm_poly (Z : Zonotope (Vec 𝕋 n)) (N : ℕ) (i : Fin n) (t : Vec ℝ Z.h) :
    (Z.taylm N i).nominal.poly t = toReal (Z.c i) + ∑ j, toReal (Z.G j i) * t j := by
  simp only [Zonotope.taylm, Taylm.nominal, Real.Taylm.poly, List.map_cons, List.map_ofFn,
    Real.Taylm.polyOf_cons, Real.Taylm.polyOf_ofFn, Real.Taylm.monomial_zero,
    Function.comp_def, Real.Taylm.monomial_single, mul_one]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.taylm_exact (Z : Zonotope (Vec 𝕋 n)) (N : ℕ) :
    Taylm.construct (Z.taylm N) = Z.construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    have hp : (fun i => toReal (Z.c i) + ∑ j, toReal (Z.G j i) * t j)
        ∈ InflatedContSet.nominalSet Z :=
      Zonotope.mem_nominalSet_iff.mpr ⟨t, ht, fun i => rfl⟩
    refine ⟨_, hp, x - fun i => toReal (Z.c i) + ∑ j, toReal (Z.G j i) * t j, fun i => ?_, ?_⟩
    · have := hx i
      rw [Zonotope.aux_taylm_poly] at this
      exact this
    · show (_ : Vec ℝ n) + (x - _) = x
      exact add_sub_cancel _ _
  -- a point of the zonotope plus its error: the coefficients are the variables
  · rintro ⟨p, hp, e, he, rfl⟩
    obtain ⟨β, hβ, hpβ⟩ := Zonotope.mem_nominalSet_iff.mp hp
    refine ⟨β, hβ, fun i => ?_⟩
    rw [Zonotope.aux_taylm_poly]
    have h2 : toReal (Z.I_error.inf i) ≤ e i ∧ e i ≤ toReal (Z.I_error.sup i) := he i
    show toReal (Z.I_error.inf i) ≤ (p + e) i - _ ∧ (p + e) i - _ ≤ toReal (Z.I_error.sup i)
    rw [Pi.add_apply, hpβ i]
    constructor <;> linarith [h2.1, h2.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
