import CORALean.ContDynamics.LinearSysDT.ReachError
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRep

/-!
# An inner approximation of a reachable set

`reachInner` is the computed run minus the error that run accumulated:
`reachInner_inner` puts it *inside* `reachSet`, the opposite direction to every
other reachability guarantee here, where the computed set is the larger one.

What this is, and is not. `reachInner` is a `Set` — `minkowskiDiff` is a
specification and computes nothing — so on its own it is a guarantee about a
set rather than an object a later step could consume. `reachInnerRep` is the
same difference at a representation: `minkDiffRep` of the run by its error, at
a generator representation `M` the caller offers and the operation checks — a
wrong `M` gives `none`, costing precision and never soundness, exactly as
`backReachForall` does. Both are noncomputable, `reduce` being so.

`minkDiffAligned` cannot take that place. It asks for equal generator counts —
the run holds `o * n`, the error one box per reducing step — and for every error
generator to be a scaled copy of the run generator at the same index, which
earlier boxes carried through `A` are not.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The computed run minus its own accumulated error — an inner approximation
of `reachSet`, as a set. -/
noncomputable def LinearSysDT.reachInner (sys : LinearSysDT ℝ n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) : Set (Vec ℝ n) :=
  minkowskiDiff (sys.reach (S := 𝒵) o ho R₀ U k).construct
    (sys.reachError o ho R₀ U k).construct

/-- The same difference at a representation, `none` where the caller's
generator representation `M` does not check out. -/
noncomputable def LinearSysDT.reachInnerRep (sys : LinearSysDT ℝ n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ)
    (M : Fin (sys.reach (S := 𝒵) o ho R₀ U k).h →
      Fin (sys.reachError o ho R₀ U k).h → ℝ) : Option (Zonotope (Vec ℝ n)) :=
  (sys.reach (S := 𝒵) o ho R₀ U k).minkDiffRep (sys.reachError o ho R₀ U k) M

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
