import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapExact

/-!
# `ConPolyZono.quadMap` is exactly the image under a quadratic map

The expansion is `PolyZonotope`'s, at a fixed factor vector: a point is one sum
once the centre is generator zero, and the product of two monomials is the
monomial of the added exponent columns. That is why the two lemmas it needs are
public there — a set equality would not do, since the constraint has to survive
with the *same* factor vector on both sides.

Which is the whole content of the theorem. The witnesses are unchanged, so the
constraint they satisfy is unchanged, and it is the same proposition before and
after because `quadMapDep` copies `A`, `b` and `EC` across.

`quadMapDep` needs an empty independent block, which `hq` asks for; `quadMap`
supplies it by running `dependent` first, and `dependent` is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix PolyZonotope

variable {n k : ℕ}

theorem ConPolyZono.quadMapDep_exact (Q : Fin k → Mat ℝ n n) (C : ConPolyZono (Vec ℝ n))
    (hq : C.q = 0) :
    quadEval Q '' C.construct = (C.quadMapDep Q).construct := by
  have hz : ∀ b : Fin C.q → ℝ, ∑ j, b j • C.GI j = 0 :=
    fun b => Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  have hquad : ∀ a : Fin C.p → ℝ,
      quadEval Q (C.c + ∑ i, monomial C.E a i • C.G i)
        = ∑ l, monomial (quadMapE C.polyZonotope) a l • quadMapG Q C.polyZonotope l := by
    intro a
    have h := PolyZonotope.quadEval_sum_ext Q C.polyZonotope a
    rw [PolyZonotope.sum_ext_eq_point C.polyZonotope a] at h
    exact h
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_, ⟨a, b, ha, _, hsat, rfl⟩, rfl⟩
    refine ⟨a, fun _ => 0, ha, fun j => j.elim0, hsat, ?_⟩
    show quadEval Q (C.c + ∑ i, monomial C.E a i • C.G i + ∑ j, b j • C.GI j)
        = (0 : Vec ℝ k)
          + (∑ l, monomial (quadMapE C.polyZonotope) a l • quadMapG Q C.polyZonotope l)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : Vec ℝ k)
    rw [hz b, add_zero, hquad a]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]
  · rintro _ ⟨a, b, ha, _, hsat, rfl⟩
    refine ⟨C.c + ∑ i, monomial C.E a i • C.G i + ∑ j, (0:ℝ) • C.GI j,
      ⟨a, fun _ => 0, ha, fun _ => by norm_num, hsat, rfl⟩, ?_⟩
    show quadEval Q (C.c + ∑ i, monomial C.E a i • C.G i + ∑ j, (0:ℝ) • C.GI j)
        = (0 : Vec ℝ k)
          + (∑ l, monomial (quadMapE C.polyZonotope) a l • quadMapG Q C.polyZonotope l)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : Vec ℝ k)
    rw [hz (fun _ => (0:ℝ)), add_zero, hquad a]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]

theorem ConPolyZono.quadMap_exact (Q : Fin k → Mat ℝ n n) (C : ConPolyZono (Vec ℝ n)) :
    quadEval Q '' C.construct = (C.quadMap Q).construct := by
  rw [C.dependent_exact]
  exact ConPolyZono.quadMapDep_exact Q C.dependent rfl

end CORALean.Real
