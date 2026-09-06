import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadEvalSumExt
import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint

/-!
# `quadMapDep` is exact where every coefficient is dependent

The two pointwise facts composed: a point is one sum, and the map of that sum is
the result's own sum. The same coefficients work in both directions, so the
image is reproduced and not enclosed.

The empty independent block is a hypothesis rather than an arrangement here;
`quadMap` is what supplies it, by running `dependent` first.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exact where every coefficient is dependent, which `quadMap` arranges. -/
theorem PolyZonotope.quadMapDep_exact (Q : Fin m → Mat ℝ n n) (S : PolyZonotope (Vec ℝ n))
    (hq : S.q = 0) :
    quadEval Q '' S.construct = (quadMapDep Q S).construct := by -- --- PROOF ---
  have hb0 : ∀ b : Fin S.q → ℝ, ∑ j, b j • S.GI j = 0 :=
    fun b => Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  have hquad : ∀ a : Fin S.p → ℝ,
      quadEval Q (S.c + ∑ i, monomial S.E a i • S.G i)
        = ∑ l, monomial (quadMapE S) a l • quadMapG Q S l := by
    intro a
    rw [← PolyZonotope.sum_ext_eq_point S a]
    exact PolyZonotope.quadEval_sum_ext Q S a
  -- both directions off `hquad`, the independent block empty by hypothesis
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_, ⟨a, b, ha, _, rfl⟩, rfl⟩
    refine ⟨a, fun _ => 0, ha, fun j => j.elim0, ?_⟩
    show quadEval Q (S.c + ∑ i, monomial S.E a i • S.G i + ∑ j, b j • S.GI j)
        = (0 : Vec ℝ m) + (∑ l, monomial (quadMapE S) a l • quadMapG Q S l)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : Vec ℝ m)
    rw [hb0 b, add_zero, hquad a]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]
  -- back, with the independent coefficients read as zero
  · rintro _ ⟨a, b, ha, _, rfl⟩
    refine ⟨S.c + ∑ i, monomial S.E a i • S.G i + ∑ j, (0:ℝ) • S.GI j,
      ⟨a, fun _ => 0, ha, fun _ => by norm_num, rfl⟩, ?_⟩
    show quadEval Q (S.c + ∑ i, monomial S.E a i • S.G i + ∑ j, (0:ℝ) • S.GI j)
        = (0 : Vec ℝ m) + (∑ l, monomial (quadMapE S) a l • quadMapG Q S l)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : Vec ℝ m)
    rw [hb0 (fun _ => 0), add_zero, hquad a]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
