module

public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMapDep
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadEvalSumExt
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint

@[expose] public section

/-!
# `quadMapDep` is exact where every coefficient is dependent

The expansion is `PolyZonotope`'s, at a fixed factor vector: a point is one sum
once the centre is generator zero, and the product of two monomials is the
monomial of the added exponent columns. That is why the two lemmas it needs are
public there — a set equality would not do, since the constraint has to survive
with the *same* factor vector on both sides.

Which is the whole content. The witnesses are unchanged, so the constraint they
satisfy is unchanged, and it is the same proposition before and after because
`quadMapDep` copies `A`, `b` and `EC` across.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.quadMapDep_exact (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n))
    (hq : cPZ.q = 0) :
    quadEval Q '' cPZ.construct = (cPZ.quadMapDep Q).construct := by -- --- PROOF ---
  have hz : ∀ b : Fin cPZ.q → ℝ, ∑ j, b j • cPZ.GI j = 0 :=
    fun b => Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  have hquad : ∀ a : Fin cPZ.p → ℝ,
      quadEval Q (cPZ.c + ∑ i, monomial cPZ.E a i • cPZ.G i)
        = ∑ l, monomial (quadMapE cPZ.polyZonotope) a l • quadMapG Q cPZ.polyZonotope l := by
    intro a
    have h := PolyZonotope.quadEval_sum_ext Q cPZ.polyZonotope a
    rw [PolyZonotope.sum_ext_eq_point cPZ.polyZonotope a] at h
    exact h
  -- both directions are `hquad` at the same `a`, the independent block being empty
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_, ⟨a, b, ha, _, hsat, rfl⟩, rfl⟩
    refine ⟨a, fun _ => 0, ha, fun j => j.elim0, hsat, ?_⟩
    show quadEval Q (cPZ.c + ∑ i, monomial cPZ.E a i • cPZ.G i + ∑ j, b j • cPZ.GI j)
        = (0 : Vec ℝ k)
          + (∑ l, monomial (quadMapE cPZ.polyZonotope) a l • quadMapG Q cPZ.polyZonotope l)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : Vec ℝ k)
    rw [hz b, add_zero, hquad a]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]
  -- back, with the independent coefficients read as zero
  · rintro _ ⟨a, b, ha, _, hsat, rfl⟩
    refine ⟨cPZ.c + ∑ i, monomial cPZ.E a i • cPZ.G i + ∑ j, (0:ℝ) • cPZ.GI j,
      ⟨a, fun _ => 0, ha, fun _ => by norm_num, hsat, rfl⟩, ?_⟩
    show quadEval Q (cPZ.c + ∑ i, monomial cPZ.E a i • cPZ.G i + ∑ j, (0:ℝ) • cPZ.GI j)
        = (0 : Vec ℝ k)
          + (∑ l, monomial (quadMapE cPZ.polyZonotope) a l • quadMapG Q cPZ.polyZonotope l)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : Vec ℝ k)
    rw [hz (fun _ => (0:ℝ)), add_zero, hquad a]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
