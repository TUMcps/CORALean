module

public import CORALean.Specification.PointSegmentSignal.Theorems.UntilSpec
public import Mathlib.Data.Bool.Basic

@[expose] public section

/-!
# The until of Boolean signals is monotone

If `λ₁ ⊑ₜ λ₁'` and `λ₂ ⊑ₜ λ₂'` at every time `t ≥ 0` (a signal that is `true` at a time is `true`
there in the primed one too), then `λ₁ U_I λ₂ ⊑ₜ λ₁' U_I λ₂'`: if the inputs are `true` at more
times, the output is `true` more often. This is the monotonicity of `U_I` of
[1, Sec. 4.2 (monotonicity)], which the paper derives from [1, Lemma 2] (`until_spec` here).

## Inputs
* `l` – left signal
* `l'` – larger left signal
* `r` – right signal
* `r'` – larger right signal
* `U` – time interval

## Hypotheses
* `hl` – the left signal is valid
* `hl'` – the larger left signal is valid
* `hr` – the right signal is valid
* `hr'` – the larger right signal is valid
* `h1` – the left signal is below its larger one
* `h2` – the right signal is below its larger one

## Conclusion
* the until is below the larger until at all times

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.until_mono (l l' r r' : PointSegmentSignal ℝ) (hl : l.IsValid)
    (hl' : l'.IsValid) (hr : r.IsValid) (hr' : r'.IsValid) (U : STLInterval ℝ)
    (h1 : ∀ t : ℝ, 0 ≤ t → l.at t ≤ l'.at t)
    (h2 : ∀ t : ℝ, 0 ≤ t → r.at t ≤ r'.at t) : -- --- CONCL ---
    ∀ t : ℝ, 0 ≤ t → (l.until U r).at t ≤ (l'.until U r').at t := by -- --- PROOF ---
  intro t ht
  obtain ⟨-, h⟩ := PointSegmentSignal.until_spec l r hl hr U
  obtain ⟨-, h'⟩ := PointSegmentSignal.until_spec l' r' hl' hr' U
  rw [Bool.le_iff_imp, h t ht, h' t ht]
  rintro ⟨t', hu, hr0, hl0⟩
  have hpos : 0 ≤ t' := by
    have := STLInterval.zero_le_of_mem_set U _ hu; linarith
  refine ⟨t', hu, Bool.le_iff_imp.1 (h2 t' hpos) hr0, fun x hx1 hx2 => ?_⟩
  exact Bool.le_iff_imp.1 (h1 x (by linarith)) (hl0 x hx1 hx2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
