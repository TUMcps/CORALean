module

public import CORALean.ContSet.Ellipsoid.Float.Operations.CartProd
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.EllipsoidIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalEllipsoidContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `Ellipsoid.cartProd` encloses the product

Each factor lies in its bounding box (`Ellipsoid.interval_contains`, given its certificate), the
product of the boxes is the box of the concatenated bounds, and a box lies in its ellipsoid
(`Interval.ellipsoid_contains`, given `σ`). Outer only, as CORA's `'outer'` mode: the product of
two ellipsoids is not an ellipsoid.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.cartProd_outer (E₁ : Ellipsoid 𝕋 n) (E₂ : Ellipsoid 𝕋 m) (s₁ : Vec 𝕋 n)
    (s₂ : Vec 𝕋 m) (σ : 𝕋)
    (hs₁ : ∀ i, toReal (E₁.Q i i) ≤ toReal (mulDown (s₁ i) (s₁ i)))
    (hs₂ : ∀ i, toReal (E₂.Q i i) ≤ toReal (mulDown (s₂ i) (s₂ i)))
    (hσ : 0 < toReal σ) (hn : ((n + m : ℕ) : ℝ) ≤ toReal (mulDown σ σ)) : -- --- CONCL ---
    (fun p : Vec ℝ n × Vec ℝ m => (Fin.append p.1 p.2 : Vec ℝ (n + m))) ''
        (E₁.construct ×ˢ E₂.construct) ⊆ (E₁.cartProd E₂ s₁ s₂ σ).construct := by -- --- PROOF ---
  rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  refine Interval.ellipsoid_contains _ σ hσ hn ?_
  have h1 := E₁.interval_contains s₁ hs₁ hx
  have h2 := E₂.interval_contains s₂ hs₂ hy
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · show toReal (Fin.append (E₁.interval s₁).inf (E₂.interval s₂).inf (Fin.castAdd m i))
        ≤ Fin.append x y (Fin.castAdd m i) ∧ Fin.append x y (Fin.castAdd m i)
        ≤ toReal (Fin.append (E₁.interval s₁).sup (E₂.interval s₂).sup (Fin.castAdd m i))
    simp only [Fin.append_left]
    exact h1 i
  · show toReal (Fin.append (E₁.interval s₁).inf (E₂.interval s₂).inf (Fin.natAdd n i))
        ≤ Fin.append x y (Fin.natAdd n i) ∧ Fin.append x y (Fin.natAdd n i)
        ≤ toReal (Fin.append (E₁.interval s₁).sup (E₂.interval s₂).sup (Fin.natAdd n i))
    simp only [Fin.append_right]
    exact h2 i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
