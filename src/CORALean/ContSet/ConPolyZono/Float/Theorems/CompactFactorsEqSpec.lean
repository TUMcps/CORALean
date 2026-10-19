module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactors
public import CORALean.ContSet.PolyZonotope.Float.Theorems.TabAtFilter

@[expose] public section

/-!
# `compactFactors` is its specification

The version that lists the used factors once and the one that rederives them at
every read are one definition: the list holds the very values the specification
recomputes, so the two differ in cost alone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [FloatOps 𝕋] in
theorem ConPolyZono.compactFactors_eq_spec (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.compactFactors = cPZ.compactFactorsSpec := by -- --- PROOF ---
  have hf : ∀ k, PolyZonotope.tabAt (Real.ConPolyZono.usedFactors cPZ.E cPZ.cons.R)
      (((List.finRange cPZ.p).filter fun k =>
        (∃ i, Real.ConPolyZono.appendE cPZ.E cPZ.cons.R k i ≠ 0 : Bool)).toArray) k
      = Real.ConPolyZono.factorIdx cPZ.E cPZ.cons.R k := fun k =>
    PolyZonotope.tabAt_filter _ _ (fun x => by
      simp [Real.ConPolyZono.usedFactors, Real.PolyZonotope.usedFactors]) k
  simp only [ConPolyZono.compactFactors, ConPolyZono.compactFactorsSpec, hf, funext hf]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
