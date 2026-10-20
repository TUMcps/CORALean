module

public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopePolyZonotopeExact
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A box as a polynomial zonotope: `polyZonotope_mono`

## Inputs
* `I₁` – inner interval
* `I₂` – outer interval

## Hypotheses
* `hord` – inner interval ordered
* `hlo` – outer lower end below inner
* `hhi` – inner upper end below outer

## Conclusion
* polynomial zonotope of the inner box is contained in the outer's
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A box inside a wider one, as polynomial zonotopes: the wider box already
holds every point the narrower one's enclosure reaches. -/
theorem Interval.polyZonotope_mono {I₁ I₂ : Interval (Vec ℝ n)}
    (hord : ∀ i, I₁.inf i ≤ I₁.sup i) (hlo : ∀ i, I₂.inf i ≤ I₁.inf i)
    (hhi : ∀ i, I₁.sup i ≤ I₂.sup i) : -- --- CONCL ---
    I₁.polyZonotope.construct ⊆ I₂.polyZonotope.construct := by -- --- PROOF ---
  simp only [Interval.polyZonotope, ← Zonotope.polyZonotope_exact]
  rintro _ ⟨β, hβ, rfl⟩
  refine I₂.zonotope_contains ?_
  intro i
  -- only the diagonal generator `i` reaches coordinate `i`
  have hsum : (∑ j : Fin n, β j •
        (fun i => if i = j then (I₁.sup i - I₁.inf i) / 2 else 0 : Vec ℝ n)) i
      = β i * ((I₁.sup i - I₁.inf i) / 2) := by
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp only [Pi.smul_apply, smul_eq_mul, if_neg (Ne.symm hj), mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  have hval : Entrywise.entry (I₁.zonotope.c + ∑ j, β j • I₁.zonotope.G j) i
      = (I₁.inf i + I₁.sup i) / 2 + β i * ((I₁.sup i - I₁.inf i) / 2) := by
    show ((fun i => (I₁.inf i + I₁.sup i) / 2 : Vec ℝ n) + ∑ j : Fin n, β j •
      (fun i => if i = j then (I₁.sup i - I₁.inf i) / 2 else 0 : Vec ℝ n)) i = _
    rw [Pi.add_apply, hsum]
  -- the coordinate is its own center plus at most its own radius, either way
  obtain ⟨hb1, hb2⟩ := abs_le.1 (hβ i)
  have hrad : 0 ≤ (I₁.sup i - I₁.inf i) / 2 := by linarith [hord i]
  rw [hval, Entrywise.entry_vec, Entrywise.entry_vec]
  exact ⟨by nlinarith [hlo i], by nlinarith [hhi i]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
