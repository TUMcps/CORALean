module

public import CORALean.ContSet.ConZonotope.Real.Theorems.Convex

@[expose] public section

/-!
# A constrained zonotope meets a hyperplane exactly between its extremes

`[1, Lemma 2]`: `Zc` meets `{x | h x = f}` iff `fmin ≤ f ≤ fmax`, `fmin`/`fmax`
the actual least and greatest values `h` takes over `Zc` — taken here as
hypotheses, exactly as the paper takes their existence for granted by writing
`min`/`max`, rather than re-derived from compactness.

Forward is `IsLeast`/`IsGreatest`'s own bound halves. Back is the paper's own
argument: a point at each extreme, and `convex_construct` puts the segment
between them inside `Zc`, at the one weight `h` reads off as `f`.

## Inputs
* `cZ` – constrained zonotope
* `h` – hyperplane normal functional
* `f` – hyperplane offset
* `fmin` – least value of the functional
* `fmax` – greatest value of the functional

## Hypotheses
* `hmin` – the least value is attained over the set
* `hmax` – the greatest value is attained over the set

## Conclusion
* the set meets the hyperplane iff the offset lies between the extremes

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mem_hyperplane_inter_iff (cZ : ConZonotope (Vec ℝ n)) (h : Vec ℝ n →ₗ[ℝ] ℝ)
    (f fmin fmax : ℝ) (hmin : IsLeast (h '' cZ.construct) fmin)
    (hmax : IsGreatest (h '' cZ.construct) fmax) :
    (∃ x ∈ cZ.construct, h x = f) ↔ fmin ≤ f ∧ f ≤ fmax := by -- --- PROOF ---
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hmin.2 ⟨x, hx, rfl⟩, hmax.2 ⟨x, hx, rfl⟩⟩
  -- back: interpolate between a point at each extreme, at the weight `h` sends to `f`
  · rintro ⟨hlo, hhi⟩
    obtain ⟨xmin, hxmin, hfmin⟩ := hmin.1
    obtain ⟨xmax, hxmax, hfmax⟩ := hmax.1
    rcases eq_or_lt_of_le (hmin.2 hmax.1) with heq | hlt
    · exact ⟨xmin, hxmin, by rw [hfmin]; linarith⟩
    · have hd : fmax - fmin ≠ 0 := (by linarith : (0:ℝ) < fmax - fmin).ne'
      set lam : ℝ := (fmax - f) / (fmax - fmin) with hlamdef
      refine ⟨lam • xmin + (1 - lam) • xmax, ?_, ?_⟩
      · refine ConZonotope.convex_construct cZ hxmin hxmax ?_ ?_ (by ring)
        · rw [hlamdef]; exact div_nonneg (by linarith) (by linarith)
        · rw [hlamdef, sub_nonneg, div_le_one (by linarith)]; linarith
      · rw [map_add, map_smul, map_smul, hfmin, hfmax, smul_eq_mul, smul_eq_mul, hlamdef]
        field_simp
        ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
