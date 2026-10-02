import CORALean.ContSet.Taylm.Real.Taylm
import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import Mathlib.Algebra.BigOperators.Pi

/-!
# A polynomial zonotope as an array of Taylor models

CORA's `taylm(polyZonotope)`: one variable per dependent factor and one per independent
generator (CORA's `blkdiag(E, I)`), coordinate `i` the polynomial `cᵢ + Σⱼ Gⱼᵢ αᴱʲ + Σₗ GIₗᵢ βₗ`,
no remainder. Exact: the box of variables is the box of factors.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}

def PolyZonotope.taylm (pZ : PolyZonotope (Vec ℝ m)) (N : ℕ) : Fin m → Taylm (pZ.p + pZ.q) :=
  fun i => ⟨(pZ.c i, 0) :: (List.ofFn (fun j => (pZ.G j i, Fin.append (fun k => pZ.E k j) 0))
    ++ List.ofFn (fun l => (pZ.GI l i, Pi.single (Fin.natAdd pZ.p l) 1))), 0, 0, N⟩


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_taylm_poly (pZ : PolyZonotope (Vec ℝ m)) (N : ℕ) (i : Fin m)
    (t : Vec ℝ (pZ.p + pZ.q)) :
    (pZ.taylm N i).poly t = pZ.c i
      + ∑ j, PolyZonotope.monomial pZ.E (fun k => t (Fin.castAdd pZ.q k)) j * pZ.G j i
      + ∑ l, t (Fin.natAdd pZ.p l) * pZ.GI l i := by -- --- PROOF ---
  have hm : ∀ j, Taylm.monomial (Fin.append (fun k => pZ.E k j) 0) t
      = PolyZonotope.monomial pZ.E (fun k => t (Fin.castAdd pZ.q k)) j := by
    intro j
    rw [Taylm.monomial, Fin.prod_univ_add]
    simp [PolyZonotope.monomial]
  simp only [PolyZonotope.taylm, Taylm.poly, Taylm.polyOf_cons, Taylm.polyOf_append,
    Taylm.polyOf_ofFn, Taylm.monomial_zero, Taylm.monomial_single, mul_one, hm]
  rw [add_assoc]
  congr 1
  congr 1
  · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · exact Finset.sum_congr rfl fun j _ => mul_comm _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.taylm_exact (pZ : PolyZonotope (Vec ℝ m)) (N : ℕ) :
    Taylm.construct (pZ.taylm N) = pZ.construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨fun k => t (Fin.castAdd pZ.q k), fun l => t (Fin.natAdd pZ.p l),
      fun k => ht _, fun l => ht _, funext fun i => ?_⟩
    have := hx i
    rw [PolyZonotope.aux_taylm_poly] at this
    change 0 ≤ _ ∧ _ ≤ 0 at this
    have hxi : x i = pZ.c i
        + ∑ j, PolyZonotope.monomial pZ.E (fun k => t (Fin.castAdd pZ.q k)) j * pZ.G j i
        + ∑ l, t (Fin.natAdd pZ.p l) * pZ.GI l i := by linarith [this.1, this.2]
    rw [hxi]
    simp [Finset.sum_apply]
  · rintro ⟨a, β, ha, hβ, rfl⟩
    refine ⟨Fin.append a β, fun k => Fin.addCases (fun k => by simpa using ha k)
      (fun l => by simpa using hβ l) k, fun i => ?_⟩
    rw [PolyZonotope.aux_taylm_poly]
    change 0 ≤ _ ∧ _ ≤ 0
    simp [Finset.sum_apply, Fin.append_left, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
