module

public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeAssignIdentifiersFrom
public import CORALean.Specification.STL.Operations.TreeToReal

@[expose] public section

/-!
# `assignIdentifiers` of a float syntax tree, read as reals

`assignIdentifiers` is `assignIdentifiersFrom` started from the empty list, which collects the
numbered non-temporal subformulas without reading a time or a number, so the list for the tree read
as reals is the list for the tree, read as reals.

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

/-- Mapping the times and numbers leaves `temporal` unchanged. -/
private theorem aux_temporal_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) :
    (φ.map f g).temporal = φ.temporal := by
  induction φ <;> simp_all [STL.Tree.temporal, STL.Tree.map]

/-- `assignIdentifiersFrom` and mapping the times and numbers. -/
private theorem aux_assignIdentifiersFrom_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n)
    (l : List (STL.Tree τ κ n)) : -- --- CONCL ---
    (φ.assignIdentifiersFrom l).map (STL.Tree.map f g) =
      (φ.map f g).assignIdentifiersFrom (l.map (STL.Tree.map f g)) := by -- --- PROOF ---
  -- induction on the tree, one case per node
  induction φ generalizing l with
  | not φ ih =>
    by_cases h : φ.temporal = true
    · simp [STL.Tree.assignIdentifiersFrom, STL.Tree.map, aux_temporal_map, h, ih]
    · simp [STL.Tree.assignIdentifiersFrom, STL.Tree.map, aux_temporal_map, h]
  | and φ ψ ihφ ihψ =>
    by_cases h : φ.temporal || ψ.temporal
    · simp only [STL.Tree.assignIdentifiersFrom, STL.Tree.map, aux_temporal_map, h, if_true,
        ihψ, ihφ]
    · simp [STL.Tree.assignIdentifiersFrom, STL.Tree.map, aux_temporal_map, h]
  | or φ ψ ihφ ihψ =>
    by_cases h : φ.temporal || ψ.temporal
    · simp only [STL.Tree.assignIdentifiersFrom, STL.Tree.map, aux_temporal_map, h, if_true,
        ihψ, ihφ]
    · simp [STL.Tree.assignIdentifiersFrom, STL.Tree.map, aux_temporal_map, h]
  -- the remaining cases
  | «until» a b φ ψ ihφ ihψ => simp only [STL.Tree.assignIdentifiersFrom, STL.Tree.map, ihψ, ihφ]
  | release a b φ ψ ihφ ihψ => simp only [STL.Tree.assignIdentifiersFrom, STL.Tree.map, ihψ, ihφ]
  | «finally» a b φ ih => simp only [STL.Tree.assignIdentifiersFrom, STL.Tree.map, ih]
  | globally a b φ ih => simp only [STL.Tree.assignIdentifiersFrom, STL.Tree.map, ih]
  | next a φ ih => simp only [STL.Tree.assignIdentifiersFrom, STL.Tree.map, ih]
  | tt => simp [STL.Tree.assignIdentifiersFrom, STL.Tree.map]
  | ff => simp [STL.Tree.assignIdentifiersFrom, STL.Tree.map]
  | cmp op e₁ e₂ => simp [STL.Tree.assignIdentifiersFrom, STL.Tree.map]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.assignIdentifiers_toReal (φ : STL.Tree 𝕋 𝕋 n) :
    φ.assignIdentifiers.map STL.Tree.toReal = φ.toReal.assignIdentifiers :=
  aux_assignIdentifiersFrom_map _ _ φ []

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
