module

@[expose] public section

/-!
# How a constrained zonotope is boxed

The boxes that keep the constraints, selectable by a value so that an algorithm which boxes a
constrained zonotope (the guard intersections) takes the method as an argument: `fm k` is
`ConZonotope.intervalTight` after `k` Fourier-Motzkin passes, `cert` is `ConZonotope.intervalCert`,
the dual certificates of the simplex, and `both k` is the intersection of the two.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- How a constrained zonotope is boxed: `k` Fourier-Motzkin passes, the simplex certificates, or
both. -/
inductive ConZonotope.BoxMethod
  | fm (k : Nat)
  | cert
  | both (k : Nat)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
