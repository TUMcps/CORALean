module

public import CORALean.ContSet.SpectraShadow.Real.Operations.CartProd
public import CORALean.ContSet.SpectraShadow.Real.Theorems.MapExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.PlusExact

@[expose] public section

/-!
# `SpectraShadow.cartProd` is exactly the Cartesian product

Read in one `Vec`, as the product ambient type is here: a pair `(x, y)` is
`Fin.append x y`. The two embeddings are linear and their sum puts `x` and `y` in
their own coordinates, so `map_exact` and `plus_exact` give the product with no
argument of its own.

## Inputs
* `S` – spectrahedral shadow
* `T` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* `SpectraShadow.cartProd` is exactly the Cartesian product
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The two embeddings, summed, are the concatenation. -/
theorem SpectraShadow.aux_pad_add (x : Vec ℝ n) (y : Vec ℝ m) :
    blockPadLeft n m x + blockPadRight n m y = Fin.append x y := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [blockPadLeft, blockPadRight]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.cartProd_exact (S : SpectraShadow (Vec ℝ n))
    (T : SpectraShadow (Vec ℝ m)) : -- --- CONCL ---
    (fun p : Vec ℝ n × Vec ℝ m => (Fin.append p.1 p.2 : Vec ℝ (n + m)))
        '' (S.construct ×ˢ T.construct) = (S.cartProd T).construct := by -- --- PROOF ---
  rw [SpectraShadow.cartProd, ← SpectraShadow.plus_exact, ← SpectraShadow.map_exact,
    ← SpectraShadow.map_exact]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, SpectraShadow.aux_pad_add x y⟩
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, (SpectraShadow.aux_pad_add x y).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
