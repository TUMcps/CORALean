module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Dependent
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemPadVarsIff

@[expose] public section

/-!
# `dependent`'s nominal set is unchanged

As in the exact layer's `dependent_exact`: the freed coefficients become the right half of the
factor vector, read by their identity exponent block and by no constraint row (`padE`), so the
slack of every row is untouched.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the nominal set is unchanged
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The dependent block and the freed one, split apart and each read back against its own
factors, coordinate by coordinate. -/
theorem ConPolyZono.aux_sum_dependent (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin (cPZ.p + cPZ.qI) → ℝ) (i : Fin n) : -- --- CONCL ---
    (∑ l, toReal (cPZ.dependent.G l i) * Real.PolyZonotope.monomial cPZ.dependent.E a l)
      = (∑ l, toReal (cPZ.G l i)
          * Real.PolyZonotope.monomial cPZ.E (fun k => a (Fin.castAdd cPZ.qI k)) l)
        + ∑ j, toReal (cPZ.GI j i) * a (Fin.natAdd cPZ.p j) := by -- --- PROOF ---
  show (∑ l : Fin (cPZ.h + cPZ.qI), toReal (Fin.append cPZ.G cPZ.GI l i)
      * Real.PolyZonotope.monomial
        (Real.PolyZonotope.plusE cPZ.E (Real.PolyZonotope.identE cPZ.qI)) a l) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Real.PolyZonotope.monomial_plusE_left,
    Real.PolyZonotope.monomial_plusE_right, Real.PolyZonotope.monomial_identE]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.nominalSet_dependent (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    nominalSet cPZ.dependent = nominalSet cPZ := by -- --- PROOF ---
  ext x
  rw [ConPolyZono.mem_nominalSet_iff, ConPolyZono.mem_nominalSet_iff]
  constructor
  · rintro ⟨a, β, ha, -, hs, hx⟩
    refine ⟨fun k => a (Fin.castAdd cPZ.qI k), fun j => a (Fin.natAdd cPZ.p j),
      fun k => ha _, fun j => ha _,
      ((PolyLevelSet.mem_padVars_iff cPZ.cons (Interval.unit cPZ.qI) a).mp hs).1,
      fun i => ?_⟩
    · have hz : ∑ j, toReal (cPZ.dependent.GI j i) * β j = 0 :=
        Finset.sum_eq_zero fun j _ => j.elim0
      rw [hx i, ConPolyZono.aux_sum_dependent, hz, add_zero, ← add_assoc]
      rfl
  -- back: the coefficients appended to the factors, the independent block now empty
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    have hA : (fun k => Fin.append a β (Fin.castAdd cPZ.qI k)) = a :=
      funext fun k => Fin.append_left a β k
    have hB : (fun j => Fin.append a β (Fin.natAdd cPZ.p j)) = β :=
      funext fun j => Fin.append_right a β j
    refine ⟨Fin.append a β, Fin.elim0,
      Fin.addCases (fun k => by simpa using ha k) (fun j => by simpa using hβ j),
      fun j => j.elim0, (PolyLevelSet.mem_padVars_iff cPZ.cons (Interval.unit cPZ.qI) _).mpr
        ⟨by rw [hA]; exact hs, by rw [hB]; exact (Interval.mem_unit_iff β).mpr hβ⟩,
      fun i => ?_⟩
    · rw [hx i]
      show _ = toReal (cPZ.c i) + (∑ l, toReal (cPZ.dependent.G l i)
          * Real.PolyZonotope.monomial cPZ.dependent.E (Fin.append a β) l)
        + ∑ j : Fin 0, toReal ((Fin.elim0 j : Vec 𝕋 n) i) * Fin.elim0 j
      rw [ConPolyZono.aux_sum_dependent, hA]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, add_assoc, Fin.append_right]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
