import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.minkDiffGenRec`

[1, Thm. 1]'s own procedure, and not an approximation: peel one generator of
`Zₛ` off at a time, intersecting the running set with its translate either way
along that generator, starting from `Zₘ` shifted by `-c⁽ˢ⁾`. `Fin.foldl` is
exactly this recursion — its initial value is the paper's `Z_int⁽¹⁾`, its step
is `Z_int⁽ⁱ⁺¹⁾`, and its result after all `pₛ` generators is `Z_int⁽ᵖˢ⁺¹⁾` — so
no bespoke recursor is needed to state it.

It returns a `Set α` and not a `Zonotope α`, deliberately: [1, Prop. 1] gives a
three-dimensional pair whose Minkowski difference is not a zonotope, so a
zonotope-valued version of this could not be exact, and exactness is the whole
claim of [1, Thm. 1]. The intermediate intersections are not zonotopes either.
So this is a specification and not a computation — what a representation can
run is `minkDiffRep`, which is inner and asks for a certificate, while this one
is proved equal to the difference in `MinkDiffGenRecExact.lean`.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


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
