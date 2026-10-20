module

public import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# What the residual does to the nominal part stays within the new generators

For `R` in `matResidual` of an interval matrix and `z` in the nominal part of a zonotope,
`|(R z)_i|` is at most the rounded-up radius `mtimesIntervalMat` gives its `i`-th new
generator: `|R_ij|` is below the larger magnitude of its two bounds and `|z_j|` below
`|c_j| + Σ|G_j|`. Holds for a constrained zonotope as well, whose nominal part sits inside the
unconstrained one.

## Inputs
* `IM` – interval matrix
* `Z` – zonotope
* `R` – matrix in the residual interval
* `z` – nominal point
* `i` – row index

## Hypotheses
* `hR` – matrix lies in the residual interval
* `hz` – point lies in the nominal set

## Conclusion
* residual image stays within the generator radius
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   08-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of the nominal zonotope reaches no further than `|c| + Σ|G|`, rounded up. -/
theorem Zonotope.aux_abs_le_nominal {Z : Zonotope (Vec 𝕋 n)} {z : Vec ℝ n}
    (hz : z ∈ nominalSet Z) (j : Fin n) :
    |z j| ≤ toReal (addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j)) := by -- --- PROOF ---
  obtain ⟨β, hβ, hzβ⟩ := Zonotope.mem_nominalSet_iff.mp hz
  have hgen := abs_sum_le_radius (d := fun i j => Z.G j i) (Δ := fun i j => toReal (Z.G j i))
    (fun _ _ => le_refl _) hβ j
  have hup := add_le_addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j)
  rw [toReal_absolute] at hup
  rw [hzβ j]
  exact le_trans (le_trans (abs_add_le _ _) (by linarith)) hup


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the residual does to the nominal part stays within the new generators' radius. -/
theorem Zonotope.abs_residual_le (IM : Interval (Mat 𝕋 m n)) {Z : Zonotope (Vec 𝕋 n)}
    {R : Mat ℝ m n}
    (hR : R ∈ (Interval.matResidual IM.inf IM.sup (Interval.centerMat IM)).construct)
    {z : Vec ℝ n} (hz : z ∈ nominalSet Z) (i : Fin m) : -- --- CONCL ---
    |(R *ᵥ z) i| ≤ toReal (sumUp fun j =>
      mulUp (maximum (absolute ((Interval.matResidual IM.inf IM.sup
          (Interval.centerMat IM)).inf i j))
        (absolute ((Interval.matResidual IM.inf IM.sup (Interval.centerMat IM)).sup i j)))
      (addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j))) := by -- --- PROOF ---
  set Rs := Interval.matResidual IM.inf IM.sup (Interval.centerMat IM)
  show |∑ j, R i j * z j| ≤ _
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (sum_le_sumUp _))
  refine Finset.sum_le_sum fun j _ => ?_
  -- each entry of the residual below the larger magnitude of its bounds
  have hRij := hR (i, j)
  simp only [Entrywise.entry_mat] at hRij
  have hab : |R i j| ≤ toReal (maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j))) := by
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs hRij.1 hRij.2
  rw [abs_mul]
  exact le_trans (mul_le_mul hab (Zonotope.aux_abs_le_nominal hz j) (abs_nonneg _)
    (le_trans (abs_nonneg _) hab)) (mul_le_mulUp _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
