import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Taylm.Float.Taylm
import Mathlib.Algebra.BigOperators.Pi

/-!
# A polynomial zonotope as an array of Taylor models, over a floating-point scalar

CORA's `taylm(polyZonotope)`: one variable per dependent factor and one per independent
generator, coordinate `i` the polynomial `cᵢ + Σⱼ Gᵢⱼ αᴱʲ + Σₗ GIᵢₗ βₗ`. The stored floats
are the coefficients unchanged, so nothing rounds, and the error box becomes the
remainder. Exact, as over ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def PolyZonotope.taylm (pZ : PolyZonotope 𝕋 n) (N : ℕ) : Fin n → Taylm 𝕋 (pZ.p + pZ.q) :=
  fun i => ⟨(pZ.c i, 0) :: (List.ofFn (fun j => (pZ.G i j, Fin.append (fun k => pZ.E k j) 0))
    ++ List.ofFn (fun l => (pZ.GI i l, Pi.single (Fin.natAdd pZ.p l) 1))),
    pZ.err.inf i, pZ.err.sup i, N⟩

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_taylm_poly (pZ : PolyZonotope 𝕋 n) (N : ℕ) (i : Fin n)
    (t : Vec ℝ (pZ.p + pZ.q)) :
    (pZ.taylm N i).nominal.poly t = toReal (pZ.c i)
      + ∑ j, toReal (pZ.G i j)
          * Real.PolyZonotope.monomial pZ.E (fun k => t (Fin.castAdd pZ.q k)) j
      + ∑ l, toReal (pZ.GI i l) * t (Fin.natAdd pZ.p l) := by -- --- PROOF ---
  have hm : ∀ j, Real.Taylm.monomial (Fin.append (fun k => pZ.E k j) 0) t
      = Real.PolyZonotope.monomial pZ.E (fun k => t (Fin.castAdd pZ.q k)) j := by
    intro j
    rw [Real.Taylm.monomial, Fin.prod_univ_add]
    simp [Real.PolyZonotope.monomial]
  simp only [PolyZonotope.taylm, Taylm.nominal, Real.Taylm.poly, List.map_cons, List.map_append,
    List.map_ofFn, Real.Taylm.polyOf_cons, Real.Taylm.polyOf_append, Real.Taylm.polyOf_ofFn,
    Real.Taylm.monomial_zero, Function.comp_def, Real.Taylm.monomial_single, mul_one, hm]
  rw [add_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.taylm_exact (pZ : PolyZonotope 𝕋 n) (N : ℕ) :
    Taylm.construct (pZ.taylm N) = pZ.construct := by -- --- PROOF ---
  ext x
  constructor
  -- a point of the range set: the variables split into the factors and the coefficients
  · rintro ⟨t, ht, hx⟩
    have hp : (fun i => toReal (pZ.c i)
        + ∑ j, toReal (pZ.G i j)
            * Real.PolyZonotope.monomial pZ.E (fun k => t (Fin.castAdd pZ.q k)) j
        + ∑ l, toReal (pZ.GI i l) * t (Fin.natAdd pZ.p l)) ∈ InflatedContSet.nominalSet pZ :=
      PolyZonotope.mem_nominalSet_iff.mpr ⟨fun k => t (Fin.castAdd pZ.q k),
        fun l => t (Fin.natAdd pZ.p l), fun k => ht _, fun l => ht _, fun i => rfl⟩
    refine ⟨_, hp, x - fun i => toReal (pZ.c i)
        + ∑ j, toReal (pZ.G i j)
            * Real.PolyZonotope.monomial pZ.E (fun k => t (Fin.castAdd pZ.q k)) j
        + ∑ l, toReal (pZ.GI i l) * t (Fin.natAdd pZ.p l), fun i => ?_, ?_⟩
    · have := hx i
      rw [PolyZonotope.aux_taylm_poly] at this
      exact this
    · show (_ : Vec ℝ n) + (x - _) = x
      exact add_sub_cancel _ _
  -- a point of the zonotope plus its error: the factors and coefficients are the variables
  · rintro ⟨p, hp, e, he, rfl⟩
    obtain ⟨a, β, ha, hβ, hpβ⟩ := PolyZonotope.mem_nominalSet_iff.mp hp
    refine ⟨Fin.append a β, fun k => Fin.addCases (fun k => by simpa using ha k)
      (fun l => by simpa using hβ l) k, fun i => ?_⟩
    rw [PolyZonotope.aux_taylm_poly]
    have h2 : toReal (pZ.err.inf i) ≤ e i ∧ e i ≤ toReal (pZ.err.sup i) := he i
    show toReal (pZ.err.inf i) ≤ (p + e) i - _ ∧ (p + e) i - _ ≤ toReal (pZ.err.sup i)
    rw [Pi.add_apply, hpβ i]
    simp only [Fin.append_left, Fin.append_right]
    constructor <;> linarith [h2.1, h2.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
