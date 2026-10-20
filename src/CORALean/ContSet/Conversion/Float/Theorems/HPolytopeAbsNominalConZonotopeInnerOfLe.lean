module

public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotopeInner

@[expose] public section

/-!
# A halfspace description as a constrained zonotope from the inside, over a floating-point scalar

## Inputs
* `P` – halfspace polytope
* `Z` – zonotope
* `y` – point
* `k` – coordinate

## Hypotheses
* `hy` – point lies in the tightened conversion

## Conclusion
* coordinate of `y` is bounded by center plus generator sums
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the tightened conversion reaches no further than `|c| + Σ|G|` of the zonotope it is
taken at, whatever the polytope. -/
theorem HPolytope.abs_nominal_conZonotopeInnerOf_le (P : HPolytope 𝕋 (Vec 𝕋 n))
    (Z : Zonotope (Vec 𝕋 n))
    {y : Vec ℝ n} (hy : y ∈ nominalSet (P.conZonotopeInnerOf Z)) (k : Fin n) : -- --- CONCL ---
    |y k| ≤
      toReal (addUp (absolute (Z.c k)) (radius (fun i j => Z.G j i) k)) := by -- --- PROOF ---
  obtain ⟨β, hβ, -, hval⟩ := ConZonotope.mem_nominalSet_iff.mp hy
  have hgen := abs_sum_le_radius (d := fun i j => Z.G j i) (Δ := fun i j => toReal (Z.G j i))
    (fun _ _ => le_refl _) hβ k
  have hup := add_le_addUp (absolute (Z.c k)) (radius (fun i j => Z.G j i) k)
  rw [toReal_absolute] at hup
  have hk : y k = toReal (Z.c k) + ∑ j, toReal (Z.G j k) * β j := hval k
  rw [hk]
  exact le_trans (abs_add_le _ _) (by linarith)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
