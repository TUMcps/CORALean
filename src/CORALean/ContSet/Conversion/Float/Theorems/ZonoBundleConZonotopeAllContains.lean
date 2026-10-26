module

public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains
public import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.Conversion.Float.Operations.ZonoBundle_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.ZonoBundleConZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A bundle's constrained zonotope, at one component, over a floating-point scalar

`ZonoBundle.conZonotopeAll_contains`: its `conZonotopeAll` contains it.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* `hk` – bundle is nonempty

## Conclusion
* bundle is contained in its constrained zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem ZonoBundle.aux_subset_interFrom {S : Set (Vec ℝ n)} : -- --- CONCL ---
    ∀ {k : ℕ} (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (Z : Fin k → Zonotope (Vec 𝕋 n)),
      S ⊆ cZ.construct → (∀ i, S ⊆ (Z i).construct) →
      S ⊆ (ZonoBundle.interFrom cZ Z).construct := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro cZ _ h _; exact h
  | succ k ih =>
    intro cZ Z h hZ
    refine ih _ _ (fun x hx => ConZonotope.intersection_outer _ _ ⟨h hx, ?_⟩) fun i => hZ i.succ
    exact Zonotope.conZonotope_contains _ (hZ 0 hx)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.conZonotopeAll_contains (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.conZonotopeAll hk).construct :=
  ZonoBundle.aux_subset_interFrom _ _ (zB.conZonotope_contains ⟨0, hk⟩)
    fun _ => zB.zonotope_contains _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
