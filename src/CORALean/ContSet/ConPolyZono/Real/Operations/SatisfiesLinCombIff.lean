import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPadEIff
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPlusIff
import CORALean.ContSet.ConPolyZono.Real.Operations.LinComb

/-!
# `ConPolyZono.linComb`'s constraint reads each side's own factors

`holds_padE_iff` first — the fresh segment factor sits at exponent zero in every
constraint monomial, so it constrains nothing — and then `holds_plus_iff` on
what is left, which is the block-diagonal system `plus` assembles.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The combination's system holds exactly when each operand's does, on the
factors it came with; the fresh factor is read by neither. -/
theorem ConPolyZono.satisfies_linComb_iff (cPZ₁ cPZ₂ : ConPolyZono α)
    (a : Fin (cPZ₁.p + cPZ₂.p + 1) → ℝ) :
    (cPZ₁.linComb cPZ₂).satisfies a ↔
      cPZ₁.satisfies (fun k => a (Fin.castAdd 1 (Fin.castAdd cPZ₂.p k)))
        ∧ cPZ₂.satisfies (fun k => a (Fin.castAdd 1 (Fin.natAdd cPZ₁.p k))) :=
  (ConPolyZono.holds_padE_iff (ConPolyZono.plusA cPZ₁.A cPZ₂.A)
      (ConPolyZono.plusB cPZ₁.b cPZ₂.b) (PolyZonotope.plusE cPZ₁.EC cPZ₂.EC) 1 a).trans
    (ConPolyZono.holds_plus_iff cPZ₁.A cPZ₁.b cPZ₁.EC cPZ₂.A cPZ₂.b cPZ₂.EC
      (fun k => a (Fin.castAdd 1 k)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
