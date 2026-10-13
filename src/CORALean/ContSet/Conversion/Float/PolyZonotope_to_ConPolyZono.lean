module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A polynomial zonotope as a constrained one, over a floating-point scalar

Nothing rounds, and nothing is computed: no constraint rows, so the system is
vacuous, and every other field is carried across.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def PolyZonotope.conPolyZono (pZ : PolyZonotope (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  m := 0
  s := 0
  c := pZ.c
  G := pZ.G
  E := pZ.E
  GI := pZ.GI
  A := fun i => i.elim0
  b := ⟨fun i => i.elim0, fun i => i.elim0⟩
  EC := fun _ => Fin.elim0
  err := pZ.err

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

-- with no constraint rows the system is vacuous
theorem PolyZonotope.conPolyZono_contains (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.conPolyZono.construct := by
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  exact ConPolyZono.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun i => i.elim0, hx⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
