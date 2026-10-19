module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.LevelSet.Real.Operations.Basic
public import CORALean.ContSet.LevelSet.Real.Operations.Lift
public import CORALean.ContSet.LevelSet.Real.Operations.SplitEquality
public import CORALean.ContSet.LevelSet.Real.Theorems.MemConstruct
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# `ContSet/LevelSet/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n : ℕ}


-- =================================  `LevelSet.append_op_eq`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Two stacked systems of equations are a system of equations (`PolyLevelSet.and_`, `cartProd`). -/
theorem LevelSet.append_op_eq {a b : ℕ} {o₁ : Fin a → CompOp} {o₂ : Fin b → CompOp}
    (h₁ : ∀ i, o₁ i = .eq) (h₂ : ∀ i, o₂ i = .eq) : ∀ i, Fin.append o₁ o₂ i = .eq :=
  Fin.addCases (fun i => (Fin.append_left _ _ i).trans (h₁ i))
    (fun i => (Fin.append_right _ _ i).trans (h₂ i))


-- ================================  `LevelSet.construct_empty`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `LevelSet.empty` denotes the empty set -/
theorem LevelSet.construct_empty (n : ℕ) : (LevelSet.empty n).construct = ∅ := by
  ext x
  simp [LevelSet.empty, LevelSet.construct, CompOp.holds]


-- =================================  `LevelSet.construct_Inf`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `LevelSet.Inf` denotes the whole space -/
theorem LevelSet.construct_Inf (n : ℕ) : (LevelSet.Inf n).construct = Set.univ := by
  ext x
  simp [LevelSet.Inf, LevelSet.construct, CompOp.holds]


-- ================================  `LevelSet.forall_fin_add`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A statement about every index of `Fin (a + b)` splits into the first `a` and the last `b`. What
the stacked constraints of `and_` and the two-sided bounds of `Interval.levelSet` need. -/
theorem LevelSet.forall_fin_add {a b : ℕ} (P : Fin (a + b) → Prop) :
    (∀ i, P i) ↔ (∀ i : Fin a, P (Fin.castAdd b i)) ∧ ∀ j : Fin b, P (Fin.natAdd a j) :=
  ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun h i => Fin.addCases h.1 h.2 i⟩


-- ==================================  `LevelSet.lift_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The lifted level set is exactly the points whose selected coordinates lie in the original. -/
theorem LevelSet.lift_exact {N : ℕ} (L : LevelSet n) (dims : Fin n → Fin N) :
    (L.lift_ dims).construct = (fun x : Vec ℝ N => fun i => x (dims i)) ⁻¹' L.construct :=
  rfl


-- =============================  `LevelSet.splitEquality_fst_op`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every constraint of the first part is an equality. -/
theorem LevelSet.splitEquality_fst_op {n : ℕ} (L : LevelSet n)
    (j : Fin L.splitEquality.1.m) : L.splitEquality.1.op j = .eq := by
  have := Finset.orderEmbOfFin_mem (Finset.univ.filter fun i => L.op i = .eq) rfl j
  exact (Finset.mem_filter.mp this).2


-- =============================  `LevelSet.splitEquality_snd_op`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- No constraint of the second part is an equality. -/
theorem LevelSet.splitEquality_snd_op {n : ℕ} (L : LevelSet n)
    (j : Fin L.splitEquality.2.m) : L.splitEquality.2.op j ≠ .eq := by
  have := Finset.orderEmbOfFin_mem (Finset.univ.filter fun i => L.op i ≠ .eq) rfl j
  exact (Finset.mem_filter.mp this).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
