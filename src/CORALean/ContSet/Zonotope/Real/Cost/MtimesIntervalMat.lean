import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
import CORALean.Global.Cost

/-!
# `Zonotope.mtimesIntervalMatCost`

Asserted, not proved, by reading `Operations/MtimesIntervalMat.lean`:

* `Interval.center`, `(inf + sup) / 2` entrywise: `2 * m * n`;
* `Interval.radius`, `(sup - inf) / 2` entrywise: `2 * m * n`;
* `absBound`, `|c j| + ∑ l, |G l j|` for each of the `n` coordinates: `h + 1`
  absolute values and `h` additions, at most `2 * h + 1` each;
* `radiusReach`, `∑ j, radius i j * absBound j` per output row: `2 * n` each,
  so `2 * m * n`;
* the centre and the `h` generators through `center *ᵥ ·`: `h + 1` products of
  `Cost.matVec m n`;
* the diagonal generator block places data and is free.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.mtimesIntervalMat` costs at `IM : Interval (Mat ℝ m n)` and
`h` generators. -/
def Zonotope.mtimesIntervalMatCost (m n h : ℕ) : Cost :=
  ⟨6 * (m * n) + n * (2 * h + 1)⟩ + (h + 1) • Cost.matVec m n

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Zonotope.mtimesIntervalMatCost_mono {h h' : ℕ} (m n : ℕ) (hh : h ≤ h') :
    Zonotope.mtimesIntervalMatCost m n h ≤
      Zonotope.mtimesIntervalMatCost m n h' := by -- --- PROOF ---
  show 6 * (m * n) + n * (2 * h + 1) + (h + 1) * (2 * (m * n)) ≤
    6 * (m * n) + n * (2 * h' + 1) + (h' + 1) * (2 * (m * n))
  exact Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul_left n (Nat.succ_le_succ (Nat.mul_le_mul_left 2 hh))) _)
    (Nat.mul_le_mul_right _ (Nat.succ_le_succ hh))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
