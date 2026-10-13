import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.halfScaled`

The constraints of `P` at the weight a parameter names. A coefficient ranges
over `[-1, 1]`, so `(t x + 1) / 2` ranges over `[0, 1]`, which is what one side
of a convex combination is scaled by; the row `A x ≤ b` becomes
`A x - (b/2) t x ≤ b/2` and the pair `t`, `-t` gives the two complementary
weights.

The parameter is a functional on the same space rather than a coordinate of its
own, so a caller that has already concatenated coefficient blocks names it with
`comap` and nothing has to be padded.

Scaling is what a cone does, not a translation: at weight zero the rows read
`A x ≤ 0` and `Ae x = 0`, which is the only reading under which an endpoint of
the combination stays reachable.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.halfScaled (t : α →ₗ[ℝ] ℝ) (P : HPolytope α) : HPolytope α where
  m := P.m
  A := fun i => P.A i - (P.b i / 2) • t
  b := fun i => P.b i / 2
  me := P.me
  Ae := fun i => P.Ae i - (P.be i / 2) • t
  be := fun i => P.be i / 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
