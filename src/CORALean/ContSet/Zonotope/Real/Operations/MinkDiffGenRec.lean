module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# `Zonotope.minkDiffGenRec`

[1, Thm. 1]'s own procedure, and not an approximation: peel one generator of `Zₛ` off at a time,
intersecting the running set with its translate either way along that generator, starting from
`Zₘ` shifted by `-c⁽ˢ⁾`. `Fin.foldl` is exactly this recursion, so no bespoke recursor is
needed. It returns a `Set α`, deliberately: [1, Prop. 1] gives a three-dimensional pair whose
Minkowski difference is not a zonotope, so a zonotope-valued version could not be exact, and the
intermediate intersections are not zonotopes either. This is a specification, not a computation —
what a representation can run is `minkDiffRep`, which is inner; this one is proved equal to the
difference in `MinkDiffGenRecExact.lean`.

## Inputs
* `Zm` – minuend
* `Zs` – subtrahend

## Output
* set from folding over the subtrahend generators

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 1]'s recursion: fold `A ↦ (A + {g⁽ˢ'ⁱ⁾}) ∩ (A - {g⁽ˢ'ⁱ⁾})` over every
generator of `Zₛ`, starting from `Zₘ.construct` shifted by `-c⁽ˢ⁾`. -/
def Zonotope.minkDiffGenRec (Zm Zs : Zonotope α) : Set α :=
  Fin.foldl Zs.h (fun A i => (A + {Zs.G i}) ∩ (A - {Zs.G i})) (Zm.construct - {Zs.c})

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
