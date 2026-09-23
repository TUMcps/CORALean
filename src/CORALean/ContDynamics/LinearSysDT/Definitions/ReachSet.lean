import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# The set a discrete run actually reaches

What `reach` encloses, written out: one linear image and one Minkowski sum per
step, both Mathlib's, so this names no operation class and no representation
computes it. That is what it is for. A support bound travels *down* an
inclusion, and every guarantee the operation classes give points the other way
— `plus_outer`, `mtimes_outer` and `reduce_outer` all say the computed set is
the *larger* one — so a bound on `R₀` and one on `U` cannot bound
`construct (reach ...)` at all. They bound this instead, which is the set a
specification is about.

`Theorems.ReachSetOuter` puts every trajectory into it, `ReachSetSubsetReach`
puts it inside `reach`, and `ReachSetBound` propagates a bound along it.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in exactly `k` steps: no `reduce`, no enclosure, and
nothing an implementation is free to widen. -/
def LinearSysDT.reachSet (sys : LinearSysDT 𝕋 n) (R₀ U : S n) : ℕ → Set (Vec ℝ n)
  | 0 => construct R₀
  | k + 1 => mulVecLin (toRealMat sys.A) '' sys.reachSet R₀ U k + construct U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
