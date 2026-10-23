module

public import CORALean.Global.Interfaces
public import Mathlib.Order.WithBot

@[expose] public section

/-!
# Two time bounds denote the same time

`TimeOrder.Eqv` extended to `WithTop T`: `inf` is only `inf`, two stored stamps are compared by
`Eqv`. At a linear order it is equality (`isEqvTop_iff_eq`); at a float scalar it compares the reals
the stamps denote, so two stamps of one real are the same time.

## Inputs
* none

## Output
* the two bounds denote the same time
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [TimeOrder T]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `inf` is only `inf`, two stored stamps compare by `Eqv`. -/
def TimeOrder.IsEqvTop : WithTop T → WithTop T → Prop
  | none, none => True
  | some a, some b => TimeOrder.Eqv a b
  | _, _ => False

/-- The comparison is decided as `Eqv` is. -/
instance (a b : WithTop T) : Decidable (TimeOrder.IsEqvTop a b) :=
  match a, b with
  | none, none => isTrue trivial
  | some a, some b => inferInstanceAs (Decidable (TimeOrder.Eqv a b))
  | none, some _ => isFalse id
  | some _, none => isFalse id

/-- Whether a bound is `inf`, decided by its form: no comparison of stamps is needed. -/
instance {T : Type} (u : WithTop T) : Decidable (u = ⊤) :=
  match u with
  | none => isTrue rfl
  | some _ => isFalse WithTop.coe_ne_top

/-- At a linear order `IsEqvTop` is equality. -/
@[simp] theorem TimeOrder.isEqvTop_iff_eq {T : Type} [LinearOrder T] (a b : WithTop T) :
    TimeOrder.IsEqvTop a b ↔ a = b := by
  cases a <;> cases b <;> simp [TimeOrder.IsEqvTop]

/-- At a linear order, an optional stamp `Eqv` to `t` is the stamp `t`. -/
@[simp] theorem TimeOrder.exists_mem_eqv_iff {T : Type} [LinearOrder T] (o : Option T) (t : T) :
    (∃ b ∈ o, TimeOrder.Eqv b t) ↔ o = some t := by
  cases o <;> simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
