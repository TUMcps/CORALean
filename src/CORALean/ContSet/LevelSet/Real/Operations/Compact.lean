module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.EmptySet.Real.EmptySet

@[expose] public section

/-!
# `LevelSet.compact_`

CORA's `@levelSet/compact_`: for a level set of exactly two equations, merge the pair when the
second is the first (`simplify(eq(1) - eq(2)) == 0`) or its negation (`simplify(eq(1) + eq(2)) ==
0`), by their operators; the pair can also be recognised as empty (`emptySet(n)`, the second
summand). Any other level set is returned as it is.

CORA tests the equalities with `simplify`, which is incomplete: it can miss an equal pair. The
test here is the equality of the two functions, the thing `simplify` approximates, so a `true`
of CORA's is a `true` here and not conversely. `compact_` is therefore noncomputable (a
classical decision on function equality), and `Theorems/CompactExact` says that it preserves the
denoted set whichever way the test falls.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
noncomputable def LevelSet.compact_ (L : LevelSet n) : LevelSet n ⊕ EmptySet n :=
  if h : L.m = 2 then
    let eq1 : Vec ℝ n → ℝ := fun x => L.f x ⟨0, by omega⟩
    let eq2 : Vec ℝ n → ℝ := fun x => L.f x ⟨1, by omega⟩
    let op1 : CompOp := L.op ⟨0, by omega⟩
    let op2 : CompOp := L.op ⟨1, by omega⟩
    let single : CompOp → LevelSet n := fun op => ⟨1, fun x _ => eq1 x, fun _ => op⟩
    if (∀ x, eq1 x - eq2 x = 0) then
      if op1 = op2 then Sum.inl (single op1)
      else if (op1 = .le ∨ op1 = .eq) ∧ (op2 = .le ∨ op2 = .eq) then Sum.inl (single .eq)
      else if (op1 = .le ∨ op1 = .lt) ∧ (op2 = .le ∨ op2 = .lt) then Sum.inl (single .lt)
      else if (op1 = .lt ∨ op1 = .eq) ∧ (op2 = .lt ∨ op2 = .eq) then Sum.inr ⟨⟩
      else Sum.inl L
    else if (∀ x, eq1 x + eq2 x = 0) then
      if (op1 = .le ∨ op1 = .eq) ∧ (op2 = .le ∨ op2 = .eq) then Sum.inl (single .eq)
      else if op1 = .lt ∨ op2 = .lt then Sum.inr ⟨⟩
      else Sum.inl L
    else Sum.inl L
  else Sum.inl L


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
