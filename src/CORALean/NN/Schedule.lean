import CORALean.NN.RefinableNetwork

/-!
# Schedules: the type, and what it denotes

A schedule is an order pattern per layer, read layer first and neuron second:
layer `0` is the network's first and the tail reads the schedule shifted. That
is CORA's order pattern tuple [1, Eq. 23], holding the refinement loop's state
and nothing else.

Plain ℕ indices rather than a `Fin` per layer: a dependent schedule would need
widths `RefinableNetwork` does not carry, and would make `tail`, `cons` and
every operation on it dependently typed for nothing. A layer reads its own
width, via `head`.

`head`, `tail` and `cons` are what a schedule denotes structurally — how one is
taken apart and put together — kept with the type itself exactly as `Interval`
keeps `construct`. What a schedule is *for* — `raise`, the refinement rules, the
loop, and reading one against a network — is `Operations/*.lean`, one file each.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- One order pattern per layer, layer `0` first and neuron second. -/
abbrev Schedule := ℕ → ℕ → ℕ

/-- The head layer's own pattern, cut to the width that layer has. -/
def Schedule.head (sch : Schedule) (n : ℕ) : OrderPattern n := fun i => sch 0 i.val

/-- What the rest of a network reads, the head layer's pattern dropped. -/
def Schedule.tail (sch : Schedule) : Schedule := fun l => sch (l + 1)

/-- A pattern in front of a schedule, which is how the induction builds one. The
indices past the layer's width are never read, so `0` will do for them. -/
def Schedule.cons (t : OrderPattern n) (sch : Schedule) : Schedule
  | 0 => fun j => if h : j < n then t ⟨j, h⟩ else 0
  | l + 1 => sch l


-- =======================================  MAIN THEOREM  ======================================= --

theorem Schedule.head_cons (t : OrderPattern n) (sch : Schedule) :
    Schedule.head (Schedule.cons t sch) n = t := by
  funext i
  -- every index of the pattern is under the width, so the padding is not reached
  exact dif_pos i.isLt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
