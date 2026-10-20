module

public import CORALean.Global.Float.ToRat
public import CORALean.Global.Tensor

@[expose] public section

/-!
# Reporting a result only if it holds no NaN

`reachFloat` and its kin conclude about `some Rs` whatever `Rs` holds. Under hardware `Float` the
guarantee rests on `Binary64.trustedHardware`, which is false of a NaN, and the argument that a run
is sound anyway needs one thing from the caller: that no float of the value it reports is a NaN
(README, "The trust base", item 2). This file lets the library make that test itself. `Floats 𝕋 α`
lists the floats a value of type `α` stores; `noNaN` is the test over that list through
`ToRat.isNaN`; `ifNoNaN` keeps a value that passes and gives `none` for one that does not;
`checkNoNaN` does so under an `Option`, which is what a `reach…Checked` entry point is: the
unchecked call, then `checkNoNaN`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- The scalars of type `𝕋` a value of type `α` stores, every one of them: a set is
reported only if none of these is a NaN. -/
class Floats (𝕋 : Type) (α : Type) where
  floats : α → List 𝕋

namespace Floats

/-- A scalar stores itself. -/
instance {𝕋 : Type} : Floats 𝕋 𝕋 := ⟨fun x => [x]⟩

/-- A vector stores the floats of its entries, or a tensor those of its slices. -/
instance {𝕋 β : Type} {n : ℕ} [Floats 𝕋 β] : Floats 𝕋 (Fin n → β) :=
  ⟨fun f => (List.ofFn fun i => floats (f i)).flatten⟩

/-- A matrix stores the floats of its rows. -/
instance {𝕋 : Type} {n m : ℕ} : Floats 𝕋 (Mat 𝕋 n m) :=
  ⟨fun M => (List.ofFn fun i => floats (𝕋 := 𝕋) (fun j => M i j)).flatten⟩

instance {𝕋 α β : Type} [Floats 𝕋 α] [Floats 𝕋 β] : Floats 𝕋 (α × β) :=
  ⟨fun p => floats p.1 ++ floats p.2⟩

/-- A pair whose first component is a label, a location or a location tuple, stores the floats
of its second: the label carries none. Tried only where `Floats 𝕋 L` has no instance. -/
instance (priority := low) {𝕋 L α : Type} [Floats 𝕋 α] : Floats 𝕋 (L × α) :=
  ⟨fun p => floats p.2⟩

instance {𝕋 α : Type} [Floats 𝕋 α] : Floats 𝕋 (List α) := ⟨fun l => (l.map floats).flatten⟩

instance {𝕋 α : Type} [Floats 𝕋 α] : Floats 𝕋 (Array α) := ⟨fun a => floats a.toList⟩

end Floats

variable {𝕋 α : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] [Floats 𝕋 α]


/-- No float `x` stores is a NaN. -/
def noNaN (x : α) : Bool := (Floats.floats (𝕋 := 𝕋) x).all fun f => !ToRat.isNaN f

/-- `x` itself if it holds no NaN, else `none`. -/
def ifNoNaN (x : α) : Option α := if noNaN (𝕋 := 𝕋) x then some x else none

/-- The result of an unchecked call, passed on only if it holds no NaN. -/
def checkNoNaN (r : Option α) : Option α := r.bind (ifNoNaN (𝕋 := 𝕋))


theorem ifNoNaN_eq_some {x y : α} (h : ifNoNaN (𝕋 := 𝕋) x = some y) :
    y = x ∧ noNaN (𝕋 := 𝕋) x = true := by
  unfold ifNoNaN at h
  split_ifs at h with hx
  exact ⟨(Option.some.inj h).symm, hx⟩

/-- A `some` of the checked call is the unchecked call's `some`, with no NaN in it. -/
theorem checkNoNaN_eq_some {r : Option α} {y : α}
    (h : checkNoNaN (𝕋 := 𝕋) r = some y) : -- --- CONCL ---
    r = some y ∧ noNaN (𝕋 := 𝕋) y = true := by -- --- PROOF ---
  unfold checkNoNaN at h
  cases r with
  | none => simp at h
  | some x =>
    obtain ⟨rfl, hx⟩ := ifNoNaN_eq_some (𝕋 := 𝕋) (by simpa using h)
    exact ⟨rfl, hx⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
