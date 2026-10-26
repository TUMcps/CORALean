module

public import CORALean.Specification.STL.Operations.TreeEliminateTrueFalseWith
public import CORALean.Specification.STL.Definitions.TreeWellFormed
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# Eliminating `true` and `false` keeps the meaning

`eliminateTrueFalse` returns a formula satisfied by the same traces whenever every time interval
is non-empty. It is `STL.Tree.aux_sat_eliminateTrueFalseWith` at the rewrite of the node
`φ U[a,b] true`, which replaces it up to meaning.

## Inputs
* `φ` – formula
* `ξ` – trace

## Hypotheses
* `hφ` – the formula is well formed

## Conclusion
* eliminating true and false keeps the meaning
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem STL.Tree.aux_sat_eliminateTrueFalseWith (ut : ℝ≥0 → ℝ≥0 → STL.Tree NNReal ℝ n →
  STL.Tree NNReal ℝ n)
    (hut : ∀ a b φ ξ, (ut a b φ).Satisfies ξ ↔ (STL.Tree.until a b φ .tt).Satisfies ξ)
    (φ : STL.Tree NNReal ℝ n) (hφ : φ.IsWellFormed) (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    (φ.eliminateTrueFalseWith ut).Satisfies ξ ↔ φ.Satisfies ξ := by -- --- PROOF ---
  induction φ generalizing ξ with
  | tt | ff | cmp => rfl
  -- each case rewrites the claim in the simplified operands, then splits the `match`
  | not φ ih =>
    have ih := ih hφ
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.Satisfies, ← ih]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    split <;> simp [STL.Tree.Satisfies]
  | and φ ψ ihφ ihψ =>
    have ihφ := ihφ hφ.1
    have ihψ := ihψ hφ.2
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.Satisfies, ← ihφ, ← ihψ]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    generalize STL.Tree.eliminateTrueFalseWith ut ψ = r
    split <;> simp [STL.Tree.Satisfies]
  | or φ ψ ihφ ihψ =>
    have ihφ := ihφ hφ.1
    have ihψ := ihψ hφ.2
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.Satisfies, ← ihφ, ← ihψ]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    generalize STL.Tree.eliminateTrueFalseWith ut ψ = r
    split <;> simp [STL.Tree.Satisfies]
  -- the temporal operators need the rewrite `hut`, and `a ≤ b` for `finally`
  | «until» a b φ ψ ihφ ihψ =>
    have ihφ := ihφ hφ.2.1
    have ihψ := ihψ hφ.2.2
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.Satisfies,
      STL.Tree.HasUntilWitness, ← ihφ, ← ihψ]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    generalize STL.Tree.eliminateTrueFalseWith ut ψ = r
    split <;> simp [STL.Tree.Satisfies, STL.Tree.HasUntilWitness, hut]
  | release a b φ ψ ihφ ihψ =>
    have ihφ := ihφ hφ.2.1
    have ihψ := ihψ hφ.2.2
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.Satisfies,
      STL.Tree.HasUntilWitness, ← ihφ, ← ihψ]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    generalize STL.Tree.eliminateTrueFalseWith ut ψ = r
    split <;> simp [STL.Tree.Satisfies, STL.Tree.HasUntilWitness]
    exact fun x _ _ _ => ⟨x, le_rfl⟩
  -- `finally` and `globally` need an instant of `[a,b]`, which `a ≤ b` gives
  | «finally» a b φ ih =>
    have ih := ih hφ.2
    have hab : ∃ t, a ≤ t ∧ t ≤ b := ⟨a, le_rfl, hφ.1⟩
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.Satisfies, STL.Tree.HasUntilWitness, ← ih]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    split <;> simp [STL.Tree.Satisfies, STL.Tree.HasUntilWitness, hab]
  | globally a b φ ih =>
    have ih := ih hφ.2
    have hab : ∃ t, a ≤ t ∧ t ≤ b := ⟨a, le_rfl, hφ.1⟩
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.Satisfies, STL.Tree.HasUntilWitness, ← ih]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    split <;> simp [STL.Tree.Satisfies, STL.Tree.HasUntilWitness, hab]
  | next a φ ih =>
    have ih := ih hφ
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.Satisfies, ← ih]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    split <;> simp [STL.Tree.Satisfies]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `eliminateTrueFalse` keeps the meaning of a formula with non-empty intervals. -/
theorem STL.Tree.sat_eliminateTrueFalse (φ : STL.Tree NNReal ℝ n) (hφ : φ.IsWellFormed)
    (ξ : ℝ≥0 → Fin n → ℝ) : φ.eliminateTrueFalse.Satisfies ξ ↔ φ.Satisfies ξ :=
  STL.Tree.aux_sat_eliminateTrueFalseWith _ (fun _ _ _ _ => Iff.rfl) φ hφ ξ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
