module

public import CORALean.ContSet.Zonotope.Real.Operations.IdentifyStep
public import CORALean.ContSet.Zonotope.Real.Theorems.IntersectStripOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.SupportDotProduct
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne

@[expose] public section

/-!
# The identification step encloses the next parameter set

[1, Sec. 3.3]: if the zonotope `X` bounds a set `P` of parameters, `AFSS_{k+1}` bounds those `P ∩
F_dk` that agree with the measurement, expanded by `γ`: `(P ∩ {θ | |rᵀθ - y| ≤ σ}) ⊕ γ Bⁿ ⊆
AFSS_{k+1}`, at every gain `λ` (the paper's recursion `FSS_{k+1} = (FSS_k ∩ F_dk) ⊕ γ Bⁿ`, [1, Sec.
3], with `P` standing for `FSS_k`). The point lies in the support strip because it lies in `X`
(`support_dotProduct`), so the tight strip loses nothing; `intersectStrip_outer` and `plus_exact`
do the rest.

## Inputs
* `X` – parameter zonotope
* `r` – regressor vector
* `y` – measurement
* `σ` – measurement error bound
* `l` – gain vector
* `γ` – expansion bounds
* `P` – parameter set

## Hypotheses
* `hP` – `P` lies in `X`

## Conclusion
* the expanded strip intersection lies in the next zonotope

## References

* [1] J. M. Bravo, T. Alamo and E. F. Camacho. "Bounded error identification of systems with
      time-varying parameters". IEEE Transactions on Automatic Control, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.identifyStep_outer (X : Zonotope (Vec ℝ n)) (r : Vec ℝ n) (y σ : ℝ)
    (l γ : Vec ℝ n) (P : Set (Vec ℝ n)) (hP : P ⊆ X.construct) : -- --- CONCL ---
    (P ∩ {θ | |r ⬝ᵥ θ - y| ≤ σ}) + {b | ∀ i, |b i| ≤ γ i} ⊆
      (X.identifyStep r y σ l γ).construct := by -- --- PROOF ---
  rintro _ ⟨θ, ⟨hθP, hθF⟩, b, hb, rfl⟩
  -- `θ` is in `X`, so its direction `rᵀθ` is between the tangent hyperplanes
  have hθX := hP hθP
  obtain ⟨⟨_, hmax⟩, ⟨_, hmin⟩⟩ := Zonotope.support_dotProduct X r
  have hhi : r ⬝ᵥ θ ≤ r ⬝ᵥ X.c + X.supportRadius r := hmax ⟨θ, hθX, rfl⟩
  have hlo : r ⬝ᵥ X.c - X.supportRadius r ≤ r ⬝ᵥ θ := hmin ⟨θ, hθX, rfl⟩
  obtain ⟨hF1, hF2⟩ := abs_le.mp (show |r ⬝ᵥ θ - y| ≤ σ from hθF)
  -- hence in the tight strip, centered at `(u + q) / 2` with half-width `(u - q) / 2`
  set q : ℝ := max (r ⬝ᵥ X.c - X.supportRadius r) (y - σ) with hq
  set u : ℝ := min (r ⬝ᵥ X.c + X.supportRadius r) (y + σ) with hu
  have hstrip : θ ∈ {x | ∀ i, |((Matrix.of fun _ j => r j : Mat ℝ 1 n) *ᵥ x -
      (fun _ : Fin 1 => (u + q) / 2)) i| ≤ (fun _ : Fin 1 => (u - q) / 2) i} := by
    intro i
    have hq' : q ≤ r ⬝ᵥ θ := max_le hlo (by linarith)
    have hu' : r ⬝ᵥ θ ≤ u := le_min hhi (by linarith)
    show |r ⬝ᵥ θ - (u + q) / 2| ≤ (u - q) / 2
    rw [abs_le]
    constructor <;> linarith
  have hθ := Zonotope.intersectStrip_outer (Matrix.of fun _ j => r j : Mat ℝ 1 n)
    (fun _ : Fin 1 => (u - q) / 2) (fun _ : Fin 1 => (u + q) / 2)
    (Matrix.of fun i _ => l i : Mat ℝ n 1) X ⟨hθX, hstrip⟩
  -- the expansion box is the zonotope with the generators `γᵢ eᵢ`
  have hbox : b ∈ ({ h := n, c := 0, G := fun i => Pi.single i (γ i) } :
      Zonotope (Vec ℝ n)).construct := by
    refine ⟨fun i => Zonotope.coefficient (γ i) (b i), fun i => ?_, ?_⟩
    · exact Zonotope.abs_coefficient_le_one ((abs_nonneg _).trans (hb i)) (hb i)
    · ext k
      simp [Finset.sum_apply, Pi.single_apply, mul_comm, Zonotope.mul_coefficient (hb k)]
  rw [Zonotope.identifyStep, ← Zonotope.plus_exact]
  exact Set.add_mem_add hθ hbox

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
