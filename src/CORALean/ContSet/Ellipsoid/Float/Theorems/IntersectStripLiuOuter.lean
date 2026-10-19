module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IntersectStripLiu
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IntersectStripGollamudiOuter

@[expose] public section

/-!
# The float Liu update encloses the intersection with the measurement set

Outer: every point `x` of `E` with `(y - c x)² / V ≤ 1` (`V > 0`) lies in
`Ellipsoid.intersectStripLiu steps E c V y λ`, for every `λ` and `steps`. Soundness needs only the
float Gollamudi theorem, which has no hypothesis on its weight, and the strip inclusion
`|c x - y| ≤ √V ≤ toReal (sqrtUp V)`; the equivalence of the two fusions at `σ²_prev = 1` explains
the choice of `λ'` but is not used. Not exact.

## Inputs
* `steps` – Newton steps per root
* `E` – ellipsoid
* `c` – measurement row
* `V` – scalar `V`
* `y` – measurement
* `lam` – update weight

## Hypotheses
* `hV` – `0 < V`

## Conclusion
* the intersection of `E` with the measurement set lies in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.intersectStripLiu_outer (steps : ℕ) (E : Ellipsoid 𝕋 n) (c : Vec 𝕋 n)
    (V y lam : 𝕋) (hV : 0 < toReal V) :
    E.construct ∩ {x | (toReal y - ∑ i, toReal (c i) * x i) ^ 2 / toReal V ≤ 1}
      ⊆ (Ellipsoid.intersectStripLiu steps E c V y lam).construct := by -- --- PROOF ---
  rintro x ⟨hxE, hxS⟩
  refine Ellipsoid.intersectStripGollamudi_outer steps E c _ y _ ⟨hxE, ?_⟩
  simp only [Set.mem_setOf_eq] at hxS ⊢
  have h1 : (toReal y - ∑ i, toReal (c i) * x i) ^ 2 ≤ toReal V := by
    rwa [div_le_one hV] at hxS
  have h2 : |toReal y - ∑ i, toReal (c i) * x i| ≤ Real.sqrt (toReal V) :=
    Real.abs_le_sqrt h1
  rw [abs_sub_comm]
  exact le_trans h2 (le_sqrtUp steps V)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
