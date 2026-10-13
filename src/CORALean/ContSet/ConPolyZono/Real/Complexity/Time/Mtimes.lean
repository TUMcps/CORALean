module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Map
public import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes

@[expose] public section

/-!
# `ConPolyZono.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` sends the centre and each of the
`h + q` generators through `M *ᵥ ·` and carries the constraint system over
unchanged, so the whole count is `mapCost` at `Cost.matVec m n`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.mtimes` costs at `M : Mat ℝ k n` and `h`, `q` generators:
one matrix-vector product for the centre and one per generator. -/
def ConPolyZono.mtimesCost (k n h q : ℕ) : Cost := ConPolyZono.mapCost (Cost.matVec k n) h q

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem ConPolyZono.mtimesCost_mono {h h' q q' : ℕ} (k n : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    ConPolyZono.mtimesCost k n h q ≤ ConPolyZono.mtimesCost k n h' q' :=
  ConPolyZono.mapCost_mono _ hh hq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
