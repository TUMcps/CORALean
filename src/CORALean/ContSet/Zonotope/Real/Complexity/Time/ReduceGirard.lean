import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReduceBy
import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard

/-!
# `Zonotope.reduceGirardCost`

Asserted, not proved, by reading `Operations/ReduceGirard.lean`. Girard's
metric on one generator is `n` absolute values and `n - 1` additions for
`‖g‖₁`, `n` more and `n` comparisons for the `max` fold, one subtraction and
one negation for the descending sort key: at most `4 * n + 2` each. Then the
`h` keys are sorted, and `reduceBy` absorbs a block of at most `h`.

No order argument: below order `o` the operation is the identity and costs
nothing, and above it the absorbed block is at most `h` wide either way, so
this bounds every `o` at once.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.reduceGirard`, and so `Zonotope.reduce`, costs at `Vec ℝ n`
on `h` generators: the metrics, the sort, and the block `reduceBy` absorbs. -/
def Zonotope.reduceGirardCost (n h : ℕ) : Cost :=
  ⟨h * (4 * n + 2)⟩ + Cost.sort h + Zonotope.reduceByCost n h

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Zonotope.reduceGirardCost_mono {h h' : ℕ} (n : ℕ) (hle : h ≤ h') :
    Zonotope.reduceGirardCost n h ≤ Zonotope.reduceGirardCost n h' := by
  refine Cost.add_le_add (Cost.add_le_add ?_ ?_) (Zonotope.reduceByCost_mono n hle)
  · exact Nat.mul_le_mul_right _ hle
  · exact Cost.sort_mono hle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
