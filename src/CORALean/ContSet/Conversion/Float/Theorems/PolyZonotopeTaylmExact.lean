module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfAppend
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import Mathlib.Algebra.BigOperators.Pi
public import CORALean.ContSet.Conversion.Float.Operations.Basic

@[expose] public section

/-!
# A polynomial zonotope as an array of Taylor models, over a floating-point scalar

CORA's `taylm(polyZonotope)`: one variable per dependent factor and one per independent
generator, coordinate `i` the polynomial `cᵢ + Σⱼ Gᵢⱼ αᴱʲ + Σₗ GIᵢₗ βₗ`. The stored floats
are the coefficients unchanged, so nothing rounds, and the error box becomes each coordinate's
error box, the remainder `[0, 0]`. Exact, as over ℝ.
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

theorem PolyZonotope.aux_taylm_poly (pZ : PolyZonotope (Vec 𝕋 n)) (N : ℕ) (i : Fin n)
    (t : Vec ℝ (pZ.p + pZ.q)) : -- --- STMT ---
    (pZ.taylm N i).inflated.poly t = toReal (pZ.c i)
      + ∑ j, toReal (pZ.G j i)
          * Real.PolyZonotope.monomial pZ.E (fun k => t (Fin.castAdd pZ.q k)) j
      + ∑ l, toReal (pZ.GI l i) * t (Fin.natAdd pZ.p l) := by -- --- PROOF ---
  have hm : ∀ j, Real.Taylm.monomial (Fin.append (fun k => pZ.E k j) 0) t
      = Real.PolyZonotope.monomial pZ.E (fun k => t (Fin.castAdd pZ.q k)) j := by
    intro j
    rw [Real.Taylm.monomial, Fin.prod_univ_add]
    simp [Real.PolyZonotope.monomial]
  simp only [PolyZonotope.taylm, Taylm.inflated, Real.Taylm.poly, List.map_cons, List.map_append,
    List.map_ofFn, Real.Taylm.polyOf_cons, Real.Taylm.polyOf_append, Real.Taylm.polyOf_ofFn,
    Real.Taylm.monomial_zero, Function.comp_def, Real.Taylm.monomial_single, mul_one, hm]
  rw [add_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.taylm_exact (pZ : PolyZonotope (Vec 𝕋 n)) (N : ℕ) :
    Taylm.construct (pZ.taylm N) = pZ.construct := by -- --- PROOF ---
  ext x
  constructor
  -- a point of the range set: the variables split into the factors and the coefficients
  · rintro ⟨t, ht, hx⟩
    have hp : (fun i => toReal (pZ.c i)
        + ∑ j, toReal (pZ.G j i)
            * Real.PolyZonotope.monomial pZ.E (fun k => t (Fin.castAdd pZ.q k)) j
        + ∑ l, toReal (pZ.GI l i) * t (Fin.natAdd pZ.p l)) ∈ InflatedContSet.nominalSet pZ :=
      PolyZonotope.mem_nominalSet_iff.mpr ⟨fun k => t (Fin.castAdd pZ.q k),
        fun l => t (Fin.natAdd pZ.p l), fun k => ht _, fun l => ht _, fun i => rfl⟩
    refine ⟨_, hp, x - fun i => toReal (pZ.c i)
        + ∑ j, toReal (pZ.G j i)
            * Real.PolyZonotope.monomial pZ.E (fun k => t (Fin.castAdd pZ.q k)) j
        + ∑ l, toReal (pZ.GI l i) * t (Fin.natAdd pZ.p l), fun i => ?_, ?_⟩
    · have := hx i
      rw [PolyZonotope.aux_taylm_poly] at this
      simp only [PolyZonotope.taylm, Taylm.inflated, toReal_zero, zero_add] at this
      exact this
    · show (_ : Vec ℝ n) + (x - _) = x
      exact add_sub_cancel _ _
  -- a point of the zonotope plus its error: the factors and coefficients are the variables
  · rintro ⟨p, hp, e, he, rfl⟩
    obtain ⟨a, β, ha, hβ, hpβ⟩ := PolyZonotope.mem_nominalSet_iff.mp hp
    refine ⟨Fin.append a β, fun k => Fin.addCases (fun k => by simpa using ha k)
      (fun l => by simpa using hβ l) k, fun i => ?_⟩
    rw [PolyZonotope.aux_taylm_poly]
    have h2 : toReal (pZ.I_error.inf i) ≤ e i ∧ e i ≤ toReal (pZ.I_error.sup i) := he i
    show toReal zero + toReal (pZ.I_error.inf i) ≤ (p + e) i - _ ∧
      (p + e) i - _ ≤ toReal zero + toReal (pZ.I_error.sup i)
    rw [toReal_zero, zero_add, zero_add, Pi.add_apply, hpβ i]
    simp only [Fin.append_left, Fin.append_right]
    constructor <;> linarith [h2.1, h2.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
