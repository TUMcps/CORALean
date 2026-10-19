module

public import CORALean.ContSet.ConPolyZono.Real.Operations.CartProd
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemCartProdIff
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import Mathlib.Algebra.Module.Prod

@[expose] public section

/-!
# `ConPolyZono.cartProd` is exactly the Cartesian product

The result is [1, Prop. 7].

The witnesses are the same as `plus_exact`'s — `Fin.append` on the factors and
on the independent coefficients, `PolyLevelSet.mem_cartProd_iff` for the constraint half — and
what differs is only what happens to the generator sum: a generator of one set
already sits at zero in the other coordinate, so the assembled sum splits along
`Prod.fst`/`Prod.snd` into the two sets' own sums rather than needing to be
identified with them, exactly as in `PolyZonotope.cartProd_exact`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       11-September-2026
-- Last update:   18-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] [Module ℝ β] in
/-- `Fin.sum_univ_add` at `cartProd`'s dependent generator count, stated through
the projection because that is the form the goal has and simp will not rewrite
a binder's type. -/
theorem ConPolyZono.aux_sum_univ_cartProd_h {cPZ₁ : ConPolyZono α} {cPZ₂ : ConPolyZono β}
    (f : Fin (cPZ₁.h + cPZ₂.h) → α × β) :
    ∑ i : Fin (cPZ₁.cartProd cPZ₂).h, f i
      = ∑ i, f (Fin.castAdd cPZ₂.h i) + ∑ i, f (Fin.natAdd cPZ₁.h i) :=
  Fin.sum_univ_add f

omit [Module ℝ α] [Module ℝ β] in
/-- The same at the independent generator count. -/
theorem ConPolyZono.aux_sum_univ_cartProd_qI {cPZ₁ : ConPolyZono α} {cPZ₂ : ConPolyZono β}
    (f : Fin (cPZ₁.qI + cPZ₂.qI) → α × β) :
    ∑ j : Fin (cPZ₁.cartProd cPZ₂).qI, f j
      = ∑ j, f (Fin.castAdd cPZ₂.qI j) + ∑ j, f (Fin.natAdd cPZ₁.qI j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.cartProd_exact (cPZ₁ : ConPolyZono α) (cPZ₂ : ConPolyZono β) :
    cPZ₁.construct ×ˢ cPZ₂.construct = (cPZ₁.cartProd cPZ₂).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro ⟨x₁, x₂⟩ ⟨⟨a₁, β₁, ha₁, hβ₁, hs₁, hx₁⟩, ⟨a₂, β₂, ha₂, hβ₂, hs₂, hx₂⟩⟩
    have hA₁ : (fun k => Fin.append a₁ a₂ (Fin.castAdd cPZ₂.p k)) = a₁ :=
      funext fun k => Fin.append_left a₁ a₂ k
    have hA₂ : (fun k => Fin.append a₁ a₂ (Fin.natAdd cPZ₁.p k)) = a₂ :=
      funext fun k => Fin.append_right a₁ a₂ k
    -- forward: appended factors and appended coefficients, each read on its own half
    refine ⟨Fin.append a₁ a₂, Fin.append β₁ β₂,
      Fin.addCases (fun k => by simpa using ha₁ k) (fun k => by simpa using ha₂ k),
      Fin.addCases (fun j => by simpa using hβ₁ j) (fun j => by simpa using hβ₂ j),
      ?_, ?_⟩
    · refine (PolyLevelSet.mem_cartProd_iff cPZ₁.cons cPZ₂.cons _).mpr ⟨?_, ?_⟩
      · rw [hA₁]; exact hs₁
      · rw [hA₂]; exact hs₂
    · rw [ConPolyZono.aux_sum_univ_cartProd_h, ConPolyZono.aux_sum_univ_cartProd_qI]
      simp only [ConPolyZono.cartProd, PolyZonotope.monomial_plusE_left,
        PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
      refine Prod.ext ?_ ?_
      · simpa only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero,
          add_zero] using hx₁
      · simpa only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero,
          zero_add] using hx₂
  -- back: the pair's equation and its constraint split apart per coordinate
  · rintro ⟨x₁, x₂⟩ ⟨a, β, ha, hβ, hsat, hxy⟩
    obtain ⟨hs₁, hs₂⟩ :=
      (PolyLevelSet.mem_cartProd_iff cPZ₁.cons cPZ₂.cons a).mp hsat
    have hx₁ : x₁ = cPZ₁.c + ∑ i, PolyZonotope.monomial cPZ₁.E (fun k => a (Fin.castAdd cPZ₂.p k)) i
              • cPZ₁.G i + ∑ j, β (Fin.castAdd cPZ₂.qI j) • cPZ₁.GI j := by
      have h1 := congrArg Prod.fst hxy
      rw [ConPolyZono.aux_sum_univ_cartProd_h, ConPolyZono.aux_sum_univ_cartProd_qI] at h1
      simpa only [ConPolyZono.cartProd, PolyZonotope.monomial_plusE_left,
        PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right, Prod.fst_add,
        Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero, add_zero] using h1
    have hx₂ : x₂ = cPZ₂.c + ∑ i, PolyZonotope.monomial cPZ₂.E (fun k => a (Fin.natAdd cPZ₁.p k)) i
              • cPZ₂.G i + ∑ j, β (Fin.natAdd cPZ₁.qI j) • cPZ₂.GI j := by
      have h2 := congrArg Prod.snd hxy
      rw [ConPolyZono.aux_sum_univ_cartProd_h, ConPolyZono.aux_sum_univ_cartProd_qI] at h2
      simpa only [ConPolyZono.cartProd, PolyZonotope.monomial_plusE_left,
        PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right, Prod.snd_add,
        Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero, zero_add] using h2
    -- the restricted factors and coefficients, one point of each set
    exact ⟨⟨fun k => a (Fin.castAdd cPZ₂.p k), fun j => β (Fin.castAdd cPZ₂.qI j),
              fun k => ha _, fun j => hβ _, hs₁, hx₁⟩,
           ⟨fun k => a (Fin.natAdd cPZ₁.p k), fun j => β (Fin.natAdd cPZ₁.qI j),
              fun k => ha _, fun j => hβ _, hs₂, hx₂⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
