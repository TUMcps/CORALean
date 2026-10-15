module

public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.SetIntersection.SetIntersection

@[expose] public section

/-!
# Zoos: the representation

CORA's `zoo` (`contSet/@zoo/zoo.m`): several range enclosures of one function, each
evaluated by its own arithmetic, whose interval enclosures `interval` intersects. CORA keeps one
object per method (`taylm(·)` four ways, `affine(·)`, `interval`); the `taylm(·)` members differ
only in the range bound, and CORA's `affine` is a Taylor model of order one, which a single
Taylor model slot cannot hold beside `taylm(int)`. A zoo here has two members: an optional Taylor
model (`taylm(int)`) and an optional interval, each over the normalized box `[-1, 1]ⁿ`.

A member encloses the function on the box: the Taylor model as `Taylm.Encloses`, the interval
as holding the function's value at every box point.

CORA's zoo is the intersection of several enclosures of one function, and so is this one: each
member denotes the set of functions it encloses (`Zoo.Member`), and the zoo denotes the
`SetIntersection` of its members' sets (`Zoo.members`), an absent member read as all functions.
`Zoo` stays a structure with named slots, not a bare `SetIntersection`, because its operations
combine the Taylor models with each other and the intervals with each other, which a list of
members does not say.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Zoo (n : ℕ) where
  taylm : Option (Taylm n)
  ivl : Option (Interval (Vec ℝ 1))

/-- One enclosure a zoo holds, as a set of functions: the Taylor model, or the interval. -/
inductive Zoo.Member (n : ℕ) where
  | taylm (T : Taylm n)
  | ivl (I : Interval (Vec ℝ 1))

/-- The functions on the box that a member encloses: for a Taylor model its `Encloses`, for an
interval those whose value at every box point it holds. -/
instance : ContSet (Zoo.Member n) (Vec ℝ n → ℝ) where
  construct
    | .taylm T => {f | T.Encloses f}
    | .ivl I => {f | ∀ t ∈ Taylm.box n, (fun _ => f t : Vec ℝ 1) ∈ I.construct}

/-- The members a zoo holds, as a `SetIntersection`: an absent member is left out, which reads
it as every function. -/
def Zoo.members (Z : Zoo n) : SetIntersection (Zoo.Member n) :=
  ⟨Z.taylm.toList.map .taylm ++ Z.ivl.toList.map .ivl⟩

/-- A zoo denotes the functions all its members enclose: CORA's intersection of enclosures. -/
instance : ContSet (Zoo n) (Vec ℝ n → ℝ) := ⟨fun Z => ContSet.construct Z.members⟩

/-- Every member encloses `f` on the box. -/
def Zoo.Encloses (Z : Zoo n) (f : Vec ℝ n → ℝ) : Prop := f ∈ Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
