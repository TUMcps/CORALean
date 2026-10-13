import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.cube`

The `□(ρ)` of [1, Lemma 1]: the sup-norm ball of radius `ρ` about the origin, "actually a
hypercube and consequently ... a zonotope", with one axis-aligned generator of length `ρ`
per coordinate. CORA writes it `zonotope(interval(-ρ·1, ρ·1))`; `Interval.zonotope` builds
the same set from a box, and this skips the box.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `□(ρ)` of [1, Lemma 1]: centre `0`, generator `j` the `j`-th unit vector scaled by `ρ`. -/
def Zonotope.cube (n : ℕ) (ρ : ℝ) : Zonotope (Vec ℝ n) where
  h := n
  c := 0
  G := fun j => Pi.single j ρ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
