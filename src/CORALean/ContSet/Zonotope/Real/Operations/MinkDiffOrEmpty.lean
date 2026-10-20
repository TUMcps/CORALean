module

public import CORALean.ContSet.OptEmpty.OptEmpty
public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRep

@[expose] public section

/-!
# `Zonotope.minkDiffOrEmpty`

`minkDiffRep` at whichever generator representation certifies one, wrapped so that the result
may be empty. No zonotope denotes `∅`, while `{0} ⊖ [-1, 1]` is `∅`, so a total
`Zonotope → Zonotope → Zonotope` cannot meet `MinkDiff`'s obligation and this one can. Two
readings of "nothing", kept apart by two types: `minkDiffRep`'s `none` says the caller's `M`
failed its check, `OptEmpty.empty` says the returned *set* is `∅`. As `MinkDiff` is inner, `∅` is
sound whatever the true difference is. Classical, and noncomputable with it: the class field takes
no candidate, so which `M` is used is a choice made here; a caller holding one calls `minkDiffRep`.

## Inputs
* `Z₁` – minuend
* `Z₂` – subtrahend

## Output
* difference zonotope, or the explicit empty set
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The difference at some certified generator representation, and the explicit
empty set where none certifies. -/
noncomputable def Zonotope.minkDiffOrEmpty (Z₁ Z₂ : Zonotope α) : OptEmpty (Zonotope α) :=
  if h : ∃ M, (Z₁.minkDiffRep Z₂ M).isSome then
    .of ((Z₁.minkDiffRep Z₂ h.choose).get h.choose_spec)
  else .empty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
