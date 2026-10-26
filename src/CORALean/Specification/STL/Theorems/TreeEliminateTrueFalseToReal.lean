module

public import CORALean.Specification.STL.Operations.TreeMap
public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeEliminateTrueFalseWith
public import CORALean.Specification.STL.Operations.TreeToReal

@[expose] public section

/-!
# `eliminateTrueFalse` of a float syntax tree, read as reals

`eliminateTrueFalse` simplifies `true` and `false` operands by the node kinds alone, so the
simplified tree read as reals is the simplification of the tree read as reals.

## Inputs
* `φ` – formula

## Hypotheses
* none

## Conclusion
* the result read as reals is the operation on the argument read as reals
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {τ τ' κ κ' : Type} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `eliminateTrueFalseWith` and mapping the times and numbers. -/
private theorem aux_eliminateTrueFalseWith_map (f : τ → τ') (g : κ → κ')
    (ut : τ → τ → STL.Tree τ κ n → STL.Tree τ κ n)
    (ut' : τ' → τ' → STL.Tree τ' κ' n → STL.Tree τ' κ' n)
    (hut : ∀ a b φ, (ut a b φ).map f g = ut' (f a) (f b) (φ.map f g))
    (φ : STL.Tree τ κ n) : -- --- CONCL ---
    (STL.Tree.eliminateTrueFalseWith ut φ).map f g =
      STL.Tree.eliminateTrueFalseWith ut' (φ.map f g) := by -- --- PROOF ---
  -- induction on the tree, one case per node
  induction φ with
  | tt => rfl
  | ff => rfl
  | cmp op e₁ e₂ => rfl
  | not φ ih =>
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.map, ← ih]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    cases l <;> simp [STL.Tree.map]
  | and φ ψ ihφ ihψ =>
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.map, ← ihφ, ← ihψ]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    generalize STL.Tree.eliminateTrueFalseWith ut ψ = r
    cases l <;> cases r <;> simp [STL.Tree.map]
  -- the remaining cases
  | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.map, ← ihφ, ← ihψ]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    generalize STL.Tree.eliminateTrueFalseWith ut ψ = r
    cases l <;> cases r <;> simp [STL.Tree.map]
  | «until» a b φ ψ ihφ ihψ =>
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.map, ← ihφ, ← ihψ]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    generalize STL.Tree.eliminateTrueFalseWith ut ψ = r
    cases l <;> cases r <;> simp [STL.Tree.map, hut]
  | release a b φ ψ ihφ ihψ =>
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.map, ← ihφ, ← ihψ]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    generalize STL.Tree.eliminateTrueFalseWith ut ψ = r
    cases l <;> cases r <;> simp [STL.Tree.map]
  -- the remaining cases
  | «finally» a b φ ih =>
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.map, ← ih]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    cases l <;> simp [STL.Tree.map]
  | globally a b φ ih =>
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.map, ← ih]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    cases l <;> simp [STL.Tree.map]
  | next a φ ih =>
    simp only [STL.Tree.eliminateTrueFalseWith, STL.Tree.map, ← ih]
    generalize STL.Tree.eliminateTrueFalseWith ut φ = l
    cases l <;> simp [STL.Tree.map]

/-- `eliminateTrueFalse` and mapping the times and numbers. -/
private theorem aux_eliminateTrueFalse_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) :
    (φ.eliminateTrueFalse).map f g = (φ.map f g).eliminateTrueFalse :=
  aux_eliminateTrueFalseWith_map f g _ _ (fun _ _ _ => rfl) φ


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.eliminateTrueFalse_toReal (φ : STL.Tree 𝕋 𝕋 n) :
    φ.eliminateTrueFalse.toReal = φ.toReal.eliminateTrueFalse :=
  aux_eliminateTrueFalse_map _ _ φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
