module

public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.SetIntersection.SetIntersection

@[expose] public section

/-!
# Zoos: the representation

CORA's `zoo` (`contSet/@zoo/zoo.m`): several range enclosures of one function, each by its own
arithmetic, whose interval enclosures `interval` intersects. CORA keeps one object per method
(`taylm(·)` four ways, `affine(·)`, `interval`); the `taylm(·)` members differ only in the range
bound, and CORA's `affine` is a Taylor model of order one. A zoo here has two members, an optional
Taylor model (`taylm(int)`) and an optional interval, over the box `[-1, 1]ⁿ` (`Taylm.Encloses`).
Each member denotes the set of functions it encloses (`Zoo.Member`), and the zoo the
`SetIntersection` of its members' sets (`Zoo.members`), an absent member read as all functions.
The `zoo` class is described in [1].

## References

* [1] [M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.](../../../../../references/2018/althoff-arch-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A zoo: an optional Taylor model and an optional interval, each an enclosure of the same
function; the zoo denotes their intersection. -/
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
