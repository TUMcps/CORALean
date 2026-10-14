module

public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# A zonotope as an array of Taylor models

CORA's `taylm(zonotope)`: one variable per generator, `c + G t` over `t ∈ [-1, 1]ʰ`, no
remainder. Exact: the box of factors is the zonotope's box of coefficients.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

def Zonotope.taylm {m : ℕ} (Z : Zonotope (Vec ℝ m)) (N : ℕ) : Fin m → Taylm Z.h :=
  fun i => ⟨(Z.c i, 0) :: List.ofFn (fun j => (Z.G j i, Pi.single j 1)), 0, 0, N⟩


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Zonotope.aux_taylm_poly {m : ℕ} (Z : Zonotope (Vec ℝ m)) (N : ℕ) (i : Fin m)
    (t : Vec ℝ Z.h) : (Z.taylm N i).poly t = Z.c i + ∑ j, t j * Z.G j i := by
  simp only [Zonotope.taylm, Taylm.poly, Taylm.polyOf_cons, Taylm.polyOf_ofFn,
    Taylm.monomial_zero, Taylm.monomial_single, mul_one]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.taylm_exact {m : ℕ} (Z : Zonotope (Vec ℝ m)) (N : ℕ) :
    Taylm.construct (Z.taylm N) = Z.construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨t, ht, funext fun i => ?_⟩
    have := hx i
    rw [Zonotope.aux_taylm_poly] at this
    change 0 ≤ _ ∧ _ ≤ 0 at this
    have hxi : x i = Z.c i + ∑ j, t j * Z.G j i := by linarith [this.1, this.2]
    rw [hxi]
    simp [Finset.sum_apply]
  · -- the generator coefficients are the variables
    rintro ⟨β, hβ, rfl⟩
    refine ⟨β, hβ, fun i => ?_⟩
    rw [Zonotope.aux_taylm_poly]
    change 0 ≤ _ ∧ _ ≤ 0
    simp [Finset.sum_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
