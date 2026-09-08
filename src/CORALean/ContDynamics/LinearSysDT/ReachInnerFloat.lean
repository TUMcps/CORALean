import CORALean.ContDynamics.LinearSysDT.ReachErrorFloat

/-!
# An inner approximation of a reachable set, from a float run

The float counterpart of `reachInner`: the computed float run minus the error
that run accumulated, put inside `reachSet` — the *exact*, real-valued
reachable set, over the nominal parts of `R₀` and `U` — by
`reachInnerFloat_inner`.

A float computation certifying something about the true reachable set is
exactly what the two-layer design is for: `reachInnerFloat` is `Set (Vec ℝ n)`,
the same real space every layer denotes into, so a check against it answers for
the exact system regardless of which layer computed the enclosure.

`minkowskiDiff` is a specification and computes nothing, exactly as at
`reachInner`, so this is a guarantee about a set rather than an object a later
step could consume — a representation-level version would first need a real
zonotope standing for the float run's *whole* construct, nominal part and error
box together, which no operation here builds; `reachErrorFloat`'s own
`Real.Zonotope` values are the model for what one would look like.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The computed float run minus its own accumulated error — an inner
approximation of the exact reachable set, as a set. -/
noncomputable def LinearSysDT.reachInnerFloat (sys : LinearSysDT 𝕋 n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope 𝕋 n) (k : ℕ) : Set (Vec ℝ n) :=
  minkowskiDiff (sys.reach (S := Zonotope 𝕋) o ho R₀ U k).construct
    (sys.reachErrorFloat o ho R₀ U k).construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
