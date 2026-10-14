module

public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.AnyTrueEqFalseOfAt

@[expose] public section

/-!
# A three-valued signal with nothing unknown is a Boolean signal

`toBoolSignal(obj)` without argument throws if some value is unknown, and otherwise is the Boolean
part: if the signal is nowhere unknown at times `t ≥ 0`, `toBoolSignal?` is `some` of it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- With nothing unknown, `toBoolSignal` is the Boolean part. -/
theorem KleeneSignal.toBoolSignal?_eq_some (s : KleeneSignal ℝ) (hs : s.IsValid)
    (h : ∀ t : ℝ, 0 ≤ t → s.at t ≠ Kleene.uu) :
    s.toBoolSignal? = some s.signal := by -- --- PROOF ---
  -- nowhere unknown means the unknown part is `false` everywhere
  have hfalse : ∀ t : ℝ, 0 ≤ t → s.isUnknown.at t = false := fun t ht => by
    by_contra hne
    exact h t ht ((KleeneSignal.at_eq_uu_iff s t).2 (by simpa using hne))
  simp [KleeneSignal.toBoolSignal?,
    PointSegmentSignal.anyTrue_eq_false_of_at s.isUnknown hs.2 hfalse]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
