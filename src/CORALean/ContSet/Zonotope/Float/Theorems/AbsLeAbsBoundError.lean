module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A coordinate of `construct` never leaves `absBoundError`

`Real.Zonotope.abs_le_absBound` at the nominal part, `addUp`-rounded, plus
whichever corner of the box is farther out — the two summed by `abs_add_le`.

## Inputs
* `Z` – zonotope
* `x` – point
* `j` – coordinate

## Hypotheses
* `hx` – point lies in the zonotope

## Conclusion
* coordinate of `x` is bounded by the absolute reach
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The nominal part never leaves the center-plus-generators bound, rounded up. -/
theorem Zonotope.aux_abs_nominal_le (Z : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ nominalSet Z) (j : Fin n) :
    |x j| ≤ toReal (addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j)) := by -- --- PROOF ---
  obtain ⟨β, hβ, hxeq⟩ := Zonotope.mem_nominalSet_iff.mp hx
  refine le_trans ?_ (add_le_addUp _ _)
  rw [hxeq j, toReal_absolute]
  refine (abs_add_le _ _).trans ?_
  gcongr
  exact abs_sum_le_radius (d := fun i j => Z.G j i) (fun _ _ => le_refl _) hβ j

/-- A point of the box never leaves whichever corner is farther from the origin. -/
theorem Zonotope.aux_abs_error_le (Z : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ (I_error Z).construct) (j : Fin n) :
    |x j| ≤ toReal (maximum (absolute (Z.I_error.inf j)) (absolute (Z.I_error.sup j)))
      := by -- --- PROOF ---
  have h : toReal (Z.I_error.inf j) ≤ x j ∧ x j ≤ toReal (Z.I_error.sup j) := hx j
  rw [toReal_maximum, toReal_absolute, toReal_absolute]
  rcases abs_cases (x j) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]; exact le_trans h.2 (le_trans (le_abs_self _) (le_max_right _ _))
  · rw [heq]; exact le_trans (neg_le_neg h.1) (le_trans (neg_le_abs _) (le_max_left _ _))


-- =======================================  MAIN THEOREM  ======================================= --

/-- A coordinate of `construct` never leaves `absBoundError`. -/
theorem Zonotope.abs_le_absBoundError {Z : Zonotope (Vec 𝕋 n)} {x : Vec ℝ n}
    (hx : x ∈ Zonotope.construct Z) (j : Fin n) :
    |x j| ≤ toReal (Zonotope.absBoundError Z j) := by -- --- PROOF ---
  obtain ⟨xnom, hxnom, xerr, hxerr, rfl⟩ := hx
  calc |xnom j + xerr j|
      ≤ |xnom j| + |xerr j| := abs_add_le _ _
    _ ≤ toReal (addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j))
        + toReal (maximum (absolute (Z.I_error.inf j)) (absolute (Z.I_error.sup j))) :=
        add_le_add (Zonotope.aux_abs_nominal_le Z hxnom j) (Zonotope.aux_abs_error_le Z hxerr j)
    _ ≤ toReal (Zonotope.absBoundError Z j) := add_le_addUp _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
