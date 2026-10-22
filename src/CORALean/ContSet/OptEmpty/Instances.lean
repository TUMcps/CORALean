module

public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.OptEmpty.OptEmpty

@[expose] public section

/-!
# What `OptEmpty` instantiates

Everything `S` gives, lifted: `empty` absorbs a binary operation and passes a unary one through,
which the class obligations survive because `∅` is a subset of everything. The operations stay
inside the instances rather than earning files of their own: each is `S`'s operation on `of`, and
`empty` everywhere else. No `Recenter`: it asks `0 ∈ construct (recenter s)` unconditionally, which
`empty` cannot meet, as for `Interval` and a crossed box. `MinkDiff` transfers, and a representation
with no `MinkDiff` of its own gets one here at the wrapper instead, as `Zonotope` does.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {S α : Type} [ContSet S α]


-- ========================================  INSTANCES  ========================================= --

/-- At a normed ambient type, where `∅` is compact and the rest is `S`'s. -/
instance [NormedAddCommGroup α] [NormedSpace ℝ α] [CompactSet S α] :
    CompactSet (OptEmpty S) α where
  isCompact_construct s := by
    cases s with
    | empty => exact isCompact_empty
    | of s => exact CompactSet.isCompact_construct s

section

variable [AddCommGroup α] [Module ℝ α]

instance [ConvexSet S α] : ConvexSet (OptEmpty S) α where
  convex_construct s := by
    cases s with
    | empty => exact convex_empty
    | of s => exact ConvexSet.convex_construct s

instance [Plus S α] : Plus (OptEmpty S) α where
  plus s t := match s, t with
    | .of s, .of t => .of (Plus.plus s t)
    | _, _ => .empty
  plus_outer s t := by
    -- a summand from `∅` is what rules the empty cases out, on either side
    cases s with
    | empty => rintro x ⟨a, ha, -⟩; exact ha.elim
    | of s => cases t with
      | empty => rintro x ⟨a, -, b, hb, -⟩; exact hb.elim
      | of t => exact Plus.plus_outer s t

instance [LinComb S α] : LinComb (OptEmpty S) α where
  linComb s t := match s, t with
    | .of s, .of t => .of (LinComb.linComb s t)
    | _, _ => .empty
  linComb_outer s t := by
    -- a segment needs an endpoint in each operand, and `∅` has none
    cases s with
    | empty => rintro x ⟨a, ha, -⟩; exact ha.elim
    | of s => cases t with
      | empty => rintro x ⟨a, -, b, hb, -⟩; exact hb.elim
      | of t => exact LinComb.linComb_outer s t

/-- The one class whose obligation is *inner*, so `empty` discharges it for
free: `∅` sits inside every difference, and claims nothing about it. -/
instance [MinkDiff S α] : MinkDiff (OptEmpty S) α where
  minkDiff s t := match s, t with
    | .of s, .of t => .of (MinkDiff.minkDiff s t)
    | _, _ => .empty
  minkDiff_inner s t := by
    cases s <;> cases t
    case of.of s t => exact MinkDiff.minkDiff_inner s t
    all_goals exact Set.empty_subset _

instance [Reduce S α] : Reduce (OptEmpty S) α where
  reduce s o := match s with
    | .empty => .empty
    | .of s => .of (Reduce.reduce s o)
  reduce_outer s o := by
    cases s with
    | empty => exact Set.Subset.refl _
    | of s => exact Reduce.reduce_outer s o

/-- A point is never the empty set, so this never returns `empty`. -/
instance [OfPoint S α] : OfPoint (OptEmpty S) α where
  ofPoint v := .of (OfPoint.ofPoint v)
  mem_ofPoint v := OfPoint.mem_ofPoint v

end

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
