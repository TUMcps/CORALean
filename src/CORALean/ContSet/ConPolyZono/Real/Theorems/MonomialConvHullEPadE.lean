module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullE
public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.ProdBlkDiag
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The hull's generator monomials ignore factors no generator reads

The convex hull of a set whose last `m` factors no generator reads (`padE E m`, as a relaxed set's
slack factors) has the generator monomials of the hull of the set without them, at the factor
vector with each copy's last `m` factors dropped: a copy's monomial is a product over that copy's
factors (`prod_blkDiag`), and the dropped ones sit at exponent zero. What lets a hull built over a
set's slack factors be read as one built without them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One copy's block, at the padded exponents and at the plain ones. -/
theorem ConPolyZono.aux_prod_blkDiag_padE {a p h m : ℕ} (E : Fin p → Fin h → ℕ)
    (v : Fin (a * (p + m)) → ℝ) (y : Fin (a * h)) : -- --- STMT ---
    (∏ x, v x ^ ConPolyZono.blkDiag a (ConPolyZono.padE E m) x y)
      = ∏ x : Fin (a * p), v (finProdFinEquiv ((finProdFinEquiv.symm x).1,
          Fin.castAdd m (finProdFinEquiv.symm x).2))
        ^ ConPolyZono.blkDiag a E x y := by -- --- PROOF ---
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective y
  rw [ConPolyZono.prod_blkDiag, ConPolyZono.prod_blkDiag, Fin.prod_univ_add]
  -- the padded factors sit at exponent zero
  have hpad : (∏ k : Fin m, v (finProdFinEquiv (j, Fin.natAdd p k))
      ^ ConPolyZono.padE E m (Fin.natAdd p k) i) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [ConPolyZono.padE, PolyZonotope.padE, Fin.append_right, pow_zero]
  rw [hpad, mul_one]
  exact Finset.prod_congr rfl fun k _ => by
    simp only [ConPolyZono.padE, PolyZonotope.padE, Fin.append_left, Equiv.symm_apply_apply]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The hull's generator monomials at padded exponents are those at the plain ones, each copy's
padded factors dropped. -/
theorem ConPolyZono.monomial_convHullE_padE {a p h m : ℕ} (E : Fin p → Fin h → ℕ)
    (v : Fin (a * (p + m) + a) → ℝ) (l : Fin (a + (a * h + a * h))) : -- --- STMT ---
    PolyZonotope.monomial (ConPolyZono.convHullE a (ConPolyZono.padE E m)) v l
      = PolyZonotope.monomial (ConPolyZono.convHullE a E)
          (Fin.append (fun x => v (Fin.castAdd a (finProdFinEquiv ((finProdFinEquiv.symm x).1,
              Fin.castAdd m (finProdFinEquiv.symm x).2))))
            fun j => v (Fin.natAdd (a * (p + m)) j)) l := by -- --- PROOF ---
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add, Fin.prod_univ_add]
  congr 1
  -- the copies' rows: a weight column reads none of them, a generator column one copy's
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · simp [ConPolyZono.convHullE]
    · refine Fin.addCases (fun y => ?_) (fun y => ?_) l <;>
        simp only [ConPolyZono.convHullE, Fin.append_left, Fin.append_right] <;>
        exact ConPolyZono.aux_prod_blkDiag_padE E (fun x => v (Fin.castAdd a x)) y
  -- the weight rows do not depend on the exponents, and read the same weight factors
  · exact Finset.prod_congr rfl fun j _ => by
      simp only [ConPolyZono.convHullE, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
