module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Sum
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# `sum` is the sum over shared factors, exactly

The point of the sum at a factor vector `a` is `pZ`'s point plus the point of every summand at
that same `a`: the dependency the Minkowski sum drops survives. The center in particular is
the plain sum of the centers, which CORA's center is not for three summands or more
(`sum_cora_counterexample`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- A summand's column keeps its monomial, read at its own factor indices. -/
theorem PolyZonotope.aux_monomial_sum (pZ : PolyZonotope α) (L : Fin m → PolyZonotope α)
    (hp : ∀ i, (L i).p = pZ.p) (a : Fin pZ.p → ℝ) (j : Fin (∑ i, (L i).h)) : -- --- STMT ---
    PolyZonotope.monomial (pZ.sum L hp).E a (Fin.natAdd pZ.h j)
      = PolyZonotope.monomial (L (finSigmaFinEquiv.symm j).1).E
          (fun k => a (Fin.cast (hp _) k)) (finSigmaFinEquiv.symm j).2 := by -- --- PROOF ---
  have hcol : ∀ k, (pZ.sum L hp).E k (Fin.natAdd pZ.h j)
      = (L (finSigmaFinEquiv.symm j).1).E (Fin.cast (hp _).symm k)
          (finSigmaFinEquiv.symm j).2 := fun k => by
    simp only [PolyZonotope.sum, Fin.append_right]
  unfold PolyZonotope.monomial
  rw [Finset.prod_congr rfl fun k _ => by rw [hcol k]]
  exact Fintype.prod_equiv (finCongr (hp _)).symm _ _ fun _ => rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.sum_point (pZ : PolyZonotope α) (L : Fin m → PolyZonotope α)
    (hp : ∀ i, (L i).p = pZ.p) (a : Fin pZ.p → ℝ) :
    (pZ.sum L hp).point a
      = pZ.point a + ∑ i, (L i).point fun k => a (Fin.cast (hp i) k) := by -- --- PROOF ---
  simp only [PolyZonotope.point, Finset.sum_add_distrib]
  show (pZ.c + ∑ i, (L i).c) + ∑ j : Fin (pZ.h + ∑ i, (L i).h),
      PolyZonotope.monomial (pZ.sum L hp).E a j • (pZ.sum L hp).G j = _
  rw [Fin.sum_univ_add]
  -- the left block is `pZ`'s own columns
  have hl : ∀ i : Fin pZ.h, PolyZonotope.monomial (pZ.sum L hp).E a (Fin.castAdd _ i)
      = PolyZonotope.monomial pZ.E a i := fun i =>
    Finset.prod_congr rfl fun k _ => by simp only [PolyZonotope.sum, Fin.append_left]
  simp only [hl, PolyZonotope.aux_monomial_sum]
  simp only [PolyZonotope.sum, Fin.append_left, Fin.append_right]
  -- the right block runs over the sigma type, one summand after the other
  rw [Equiv.sum_comp finSigmaFinEquiv.symm
    (fun x : (Σ i, Fin (L i).h) => PolyZonotope.monomial (L x.1).E
      (fun k => a (Fin.cast (hp _) k)) x.2 • (L x.1).G x.2), Fintype.sum_sigma]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
