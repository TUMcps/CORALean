import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.Global.Cost

/-!
# `Zonotope.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` sends the centre and each of the
`h` generators through `M *ᵥ ·`, so it pays `h + 1` matrix-vector products at
`m × n` and nothing else.

`mtimesCost_mono` is what lets a caller use a *bound* on `h` rather than `h`
itself, which is how the reachability bound in `ContDynamics/` is assembled.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.mtimes` costs at `M : Mat ℝ m n` and `h` generators: one
matrix-vector product for the centre and one per generator. -/
def Zonotope.mtimesCost (m n h : ℕ) : Cost := (h + 1) • Cost.matVec m n

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Zonotope.mtimesCost_mono {h h' : ℕ} (m n : ℕ) (hle : h ≤ h') :
    Zonotope.mtimesCost m n h ≤ Zonotope.mtimesCost m n h' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ hle)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
