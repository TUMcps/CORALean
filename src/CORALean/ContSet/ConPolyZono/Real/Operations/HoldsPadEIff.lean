module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE

@[expose] public section

/-!
# `padE` constrains nothing new

Fresh factors at exponent zero constrain nothing, so the system says of the
widened factor vector exactly what it said of the original.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Fresh factors at exponent zero constrain nothing, so the system says of the
widened factor vector exactly what it said of the original. -/
theorem ConPolyZono.holds_padE_iff {p m s : ℕ} (A : Mat ℝ m s) (b : Interval (Vec ℝ m))
    (EC : Fin p → Fin s → ℕ) (r : ℕ) (a : Fin (p + r) → ℝ) :
    ConPolyZono.holds A b (ConPolyZono.padE EC r) a
      ↔ ConPolyZono.holds A b EC (fun k => a (Fin.castAdd r k)) := by
  have hm : PolyZonotope.monomial (ConPolyZono.padE EC r) a
      = PolyZonotope.monomial EC (fun k => a (Fin.castAdd r k)) :=
    funext fun l => ConPolyZono.monomial_padE EC r a l
  simp only [ConPolyZono.holds, hm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
