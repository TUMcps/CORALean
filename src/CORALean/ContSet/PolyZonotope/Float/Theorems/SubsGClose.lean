module

public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.ContSet.PolyZonotope.Float.Operations.Subs

@[expose] public section

/-!
# The stored generators of `subs` are close to the exact ones

A coefficient in a term's bracket times the original generator's entry is between the two directed
products, which are `aux_subsGDiff` apart, so it is within that of the stored (rounded-down) one.

## Inputs
* `pZ` – polynomial zonotope
* `nu` – number of substituted factors
* `pZin` – polynomial zonotope substituted in
* `idu` – indices of the substituted factors
* `l` – term index
* `r` – coordinate
* `ρ` – coefficient value

## Hypotheses
* `h₁` – coefficient is at least the lower endpoint
* `h₂` – coefficient is at most the upper endpoint

## Conclusion
* stored generator is within its gap of the exact one
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.subsG_close (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ}
    (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) (l : Fin (pZ.subsTerms pZin idu).length) (r : Fin n) {ρ : ℝ}
    (h₁ : toReal ((pZ.subsTerms pZin idu).get l).2.1.inf ≤ ρ)
    (h₂ : ρ ≤ toReal ((pZ.subsTerms pZin idu).get l).2.1.sup) : -- --- CONCL ---
    |ρ * toReal (pZ.G ((pZ.subsTerms pZin idu).get l).1 r) - toReal (pZ.aux_subsGDown pZin idu r l)|
      ≤ toReal (pZ.aux_subsGDiff pZin idu r l) := by -- --- PROOF ---
  have hb := Real.Interval.mul_between_corners h₁ h₂
    (le_refl (toReal (pZ.G ((pZ.subsTerms pZin idu).get l).1 r)))
    (le_refl (toReal (pZ.G ((pZ.subsTerms pZin idu).get l).1 r)))
  have hlo := le_trans (Interval.mulLo_le _ _ _ _) hb.1
  have hhi := le_trans hb.2 (Interval.le_mulHi _ _ _ _)
  have hgap := sub_le_subUp (Interval.mulHi ((pZ.subsTerms pZin idu).get l).2.1.inf
    ((pZ.subsTerms pZin idu).get l).2.1.sup (pZ.G ((pZ.subsTerms pZin idu).get l).1 r)
    (pZ.G ((pZ.subsTerms pZin idu).get l).1 r)) (pZ.aux_subsGDown pZin idu r l)
  rw [abs_le]
  simp only [PolyZonotope.aux_subsGDiff, PolyZonotope.aux_subsGDown] at hgap ⊢
  constructor <;> linarith [hlo, hhi, hgap]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
