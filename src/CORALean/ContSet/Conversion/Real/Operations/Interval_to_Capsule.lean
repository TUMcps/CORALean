module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# A box as a capsule
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The capsule with the segment along axis `k` and the ball covering the other half-widths. -/
noncomputable def Interval.capsuleAlong (I : Interval (Vec ℝ n)) (k : Fin n) : Capsule n where
  c := fun i => (I.inf i + I.sup i) / 2
  g := fun i => if i = k then (I.sup i - I.inf i) / 2 else 0
  r := Real.sqrt (∑ i, if i = k then 0 else ((I.sup i - I.inf i) / 2) ^ 2)

/-- CORA's `capsule(interval)`: the segment runs along a widest edge, the first one of maximal
width. The choice is a computable `List.argmax` over the axes; only the real arithmetic is
noncomputable. For `n = 0` there is no axis and the capsule is the point. -/
noncomputable def Interval.capsule (I : Interval (Vec ℝ n)) : Capsule n :=
  match (List.finRange n).argmax (fun i => I.sup i - I.inf i) with
  | some k => I.capsuleAlong k
  | none => ⟨0, 0, 0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
