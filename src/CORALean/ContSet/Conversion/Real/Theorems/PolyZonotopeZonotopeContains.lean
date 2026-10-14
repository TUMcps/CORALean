module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Logic.Function.CompTypeclasses
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope

@[expose] public section

/-!
# A polynomial zonotope as a zonotope

`PolyZonotope.zonotope_contains`: its `zonotope` contains it.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at the generator count this conversion produces, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
theorem PolyZonotope.aux_sum_univ_zonotope {pZ : PolyZonotope α} (f : Fin (pZ.h + pZ.q) → α) :
    ∑ l : Fin pZ.zonotope.h, f l
      = ∑ i, f (Fin.castAdd pZ.q i) + ∑ j, f (Fin.natAdd pZ.h j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.zonotope_contains (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.zonotope.construct := by -- --- PROOF ---
  rintro _ ⟨a, b, ha, hb, rfl⟩
  refine ⟨Fin.append (PolyZonotope.monomial pZ.E a) b, ?_, ?_⟩
  · refine Fin.addCases ?_ ?_
    · intro i
      simpa using PolyZonotope.abs_monomial_le_one pZ.E ha i
    · intro j
      simpa using hb j
  · rw [PolyZonotope.aux_sum_univ_zonotope]
    simp only [PolyZonotope.zonotope, Fin.append_left, Fin.append_right]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
