import CORALean.ContSet.Taylm.Real.Taylm
import CORALean.ContSet.Interval.Real.Interval

/-!
# Zoos: the representation

CORA's `zoo` (`contSet/@zoo/zoo.m`): several range enclosures of one function, each
evaluated by its own arithmetic, whose interval enclosures `interval` intersects. CORA keeps
a sorted list of method names and an object per method, from `taylm(int)`, `taylm(bnb)`,
`taylm(bnbAdv)`, `taylm(linQuad)`, `affine(int)`, `affine(bnb)`, `affine(bnbAdv)` and
`interval`; the four `taylm(·)` members run the same arithmetic and differ in the range
bound `interval` takes, and CORA's `affine` is a different representation (affine arithmetic
with fresh noise symbols per operation), which is not `Taylm` at order one. A zoo here has
the two members that exist: an optional Taylor model (`taylm(int)`) and an optional interval
(`interval`), each over the normalized box `[-1, 1]ⁿ` of `Taylm`.

A member encloses the function on the box: the Taylor model as `Taylm.Encloses`, the interval
as holding the function's value at every box point.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Zoo (n : ℕ) where
  taylm : Option (Taylm n)
  ivl : Option (Interval (Vec ℝ 1))

/-- Every member encloses `f` on the box. -/
def Zoo.Encloses (Z : Zoo n) (f : Vec ℝ n → ℝ) : Prop :=
  (∀ T, Z.taylm = some T → T.Encloses f) ∧
    ∀ I, Z.ivl = some I → ∀ t ∈ Taylm.box n, (fun _ => f t : Vec ℝ 1) ∈ I.construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
