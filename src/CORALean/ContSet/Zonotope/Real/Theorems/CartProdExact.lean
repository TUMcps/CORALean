module

public import CORALean.ContSet.Zonotope.Real.Operations.CartProd
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Prod

@[expose] public section

/-!
# `Zonotope.cartProd` is exactly the Cartesian product

The witness is `Fin.append β₁ β₂`, as for `plus_exact`; a generator of one set sits at zero in
the other coordinate, so the assembled sum splits along `Prod.fst` and `Prod.snd` into the two
sets' own sums.

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope

## Hypotheses
* none

## Conclusion
* the product set equals the zonotope of `cartProd`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] [Module ℝ β] in
/-- `Fin.sum_univ_add` at `cartProd`'s generator count, stated through the projection
because that is the form the goal has. -/
theorem Zonotope.aux_sum_univ_cartProd {Z₁ : Zonotope α} {Z₂ : Zonotope β}
    (f : Fin (Z₁.h + Z₂.h) → α × β) :
    ∑ j : Fin (Z₁.cartProd Z₂).h, f j
      = ∑ j, f (Fin.castAdd Z₂.h j) + ∑ j, f (Fin.natAdd Z₁.h j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cartProd_exact (Z₁ : Zonotope α) (Z₂ : Zonotope β) :
    Z₁.construct ×ˢ Z₂.construct = (Z₁.cartProd Z₂).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro ⟨x₁, x₂⟩ ⟨⟨β₁, hβ₁, rfl⟩, ⟨β₂, hβ₂, rfl⟩⟩
    refine ⟨Fin.append β₁ β₂, Fin.addCases (fun l => by simpa using hβ₁ l)
      (fun l => by simpa using hβ₂ l), ?_⟩
    rw [Zonotope.aux_sum_univ_cartProd]
    simp only [Zonotope.cartProd, Fin.append_left, Fin.append_right, Prod.smul_mk, smul_zero]
    refine Prod.ext ?_ ?_ <;> simp [Prod.fst_sum, Prod.snd_sum]
  -- back: the two halves of `β` are the two zonotopes' own coefficients
  · rintro x ⟨β, hβ, rfl⟩
    refine ⟨⟨fun j => β (Fin.castAdd Z₂.h j), fun j => hβ _, ?_⟩,
            ⟨fun j => β (Fin.natAdd Z₁.h j), fun j => hβ _, ?_⟩⟩
    · rw [Zonotope.aux_sum_univ_cartProd]
      simp [Zonotope.cartProd, Fin.append_left, Fin.append_right, Prod.fst_sum]
    · rw [Zonotope.aux_sum_univ_cartProd]
      simp [Zonotope.cartProd, Fin.append_left, Fin.append_right, Prod.snd_sum]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
