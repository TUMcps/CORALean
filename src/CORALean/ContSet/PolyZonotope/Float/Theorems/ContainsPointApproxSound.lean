module

public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.PolyZonotope.Float.Operations.ContainsPointApprox
public import CORALean.ContSet.PolyZonotope.Float.Theorems.CentreMemConstruct
public import CORALean.ContSet.PolyZonotope.Float.Theorems.InnerGeneralSubsetImage
public import CORALean.ContSet.PolyZonotope.Float.Theorems.IndepFactorsPointMem

@[expose] public section

/-!
# `containsPointApprox` proves membership

`true` puts the point in the polynomial zonotope. At the centre, no zero exponent column makes
every monomial vanish at the zero factors (`centre_mem_construct`). Otherwise `innerGeneral`
puts the point in the image of `[-1, 1]ᵖ⁺ᵍ` under the point map of `indepFactors`, which stays
in the nominal set (`indepFactors_point_mem`); the error box holds `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.containsPointApprox_sound (pZ : PolyZonotope (Vec 𝕋 n)) (s : Vec 𝕋 n)
    (start : Vec 𝕋 (pZ.p + pZ.q)) (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter : ℕ)
    (h : PolyZonotope.containsPointApprox pZ s start inv iter = true) :
    toRealVec s ∈ pZ.construct := by -- --- PROOF ---
  unfold PolyZonotope.containsPointApprox at h
  dsimp only at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨herr, hrest⟩ := h
  -- `0` is in the error box
  have h0 : ∀ i, toReal (pZ.I_error.inf i) ≤ 0 ∧ 0 ≤ toReal (pZ.I_error.sup i) := fun i => by
    have h := List.all_eq_true.mp herr i (List.mem_finRange i)
    simp only [Bool.and_eq_true] at h
    exact ⟨le_of_le_of_eq (toReal_le_of_le h.1) toReal_zero,
      le_of_eq_of_le toReal_zero.symm (toReal_le_of_le h.2)⟩
  rcases hrest with hc | hg
  · -- the centre, with no zero exponent column
    obtain ⟨hs, hE⟩ := hc
    have hsc : toRealVec s = toRealVec pZ.c := funext fun i => by
      have h := List.all_eq_true.mp hs i (List.mem_finRange i)
      simp only [Bool.and_eq_true] at h
      exact le_antisymm (toReal_le_of_le h.1) (toReal_le_of_le h.2)
    have hE' : Real.ConPolyZono.NoZeroCol pZ.E := fun l => by
      obtain ⟨k, -, hk⟩ := List.any_eq_true.mp (List.all_eq_true.mp hE l (List.mem_finRange l))
      exact ⟨k, by simpa using hk⟩
    rw [hsc]
    exact PolyZonotope.centre_mem_construct pZ hE' h0
  · -- the point is the lifted map's value at some `(α, β)` of the unit box
    obtain ⟨a, ha, hpt⟩ := PolyZonotope.innerGeneral_subset_image _ _ _ _ inv iter hg
      (Interval.mem_point s)
    -- the factors are in `[-1, 1]`
    have hab : ∀ k, |a k| ≤ 1 := fun k => by
      have h1 : toReal (neg one : 𝕋) ≤ a k := (ha k).1
      have h2 : a k ≤ toReal (one : 𝕋) := (ha k).2
      rw [toReal_neg, toReal_one] at h1
      rw [toReal_one] at h2
      exact abs_le.mpr ⟨h1, h2⟩
    refine ⟨toRealVec s, ?_, 0, h0, add_zero _⟩
    have h := PolyZonotope.indepFactors_point_mem pZ hab
    rw [hpt] at h
    exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
