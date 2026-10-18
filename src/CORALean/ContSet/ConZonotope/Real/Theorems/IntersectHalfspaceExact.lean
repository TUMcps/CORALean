module

public import CORALean.ContSet.ConZonotope.Real.Operations.IntersectHalfspace
public import CORALean.ContSet.ConZonotope.Real.Operations.MemOfMatIff
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# `Zonotope.interHalfspace` is exactly the halfspace intersection

`[1, Thm. 1]`: given that `Z` actually meets the hyperplane `{x | h x = f}` — the paper's own
hypothesis, carried by `Lemma 1`'s inequality there but stated directly here as the intersection
itself — `Z.interHalfspace h f` denotes exactly `Z.construct ∩ {x | h x ≤ f}`.

`aux_dm_nonneg` is the paper's own first step: the hypothesis, the definition of `dm`, and the
triangle inequality over `Z`'s generators force `dm ≥ 0`. From there both inclusions are a single
linear combination of `dm ≥ 0` with the fresh coefficient's own bound `|t| ≤ 1` — no case split on
`dm = 0` is needed, since `t`'s bound already absorbs it (and, on the `⊇` side, Lean's own
`x / 0 = 0` makes the paper's formula for `t` land on a valid witness there too).

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add`/`Fin.sum_univ_one` at the one row `interHalfspace`'s constraint matrix
carries. -/
theorem Zonotope.aux_mulVec_interHalfspace (Z : Zonotope (Vec ℝ n)) (h : Vec ℝ n →ₗ[ℝ] ℝ) (f : ℝ)
    (ξ : Fin (Z.h + 1) → ℝ) : -- --- STMT ---
    ((fun _ : Fin 1 => Fin.append (fun i => h (Z.G i))
        (fun _ : Fin 1 => (f - h Z.c + ∑ i, |h (Z.G i)|) / 2)) *ᵥ ξ) 0
      = (∑ i, h (Z.G i) * ξ (Fin.castAdd 1 i))
        + (f - h Z.c + ∑ i, |h (Z.G i)|) / 2 * ξ (Fin.natAdd Z.h 0) := by -- --- PROOF ---
  show ∑ j : Fin (Z.h + 1), Fin.append (fun i => h (Z.G i))
      (fun _ : Fin 1 => (f - h Z.c + ∑ i, |h (Z.G i)|) / 2) j * ξ j = _
  rw [Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [Fin.append_left, Fin.append_right]

/-- The fresh generator is `0`: only `Z`'s own generators, at `Z`'s own coefficients, contribute
to the value. -/
theorem Zonotope.aux_value_interHalfspace (Z : Zonotope (Vec ℝ n)) (ξ : Fin (Z.h + 1) → ℝ) :
    Z.c + ∑ j, ξ j • (Fin.append Z.G (fun _ : Fin 1 => (0 : Vec ℝ n))) j
      = Z.c + ∑ i, ξ (Fin.castAdd 1 i) • Z.G i := by
  congr 1
  rw [Fin.sum_univ_add, Fin.sum_univ_one]
  simp

/-- Membership in `Z.interHalfspace h f`, unpacked into `Z`'s own coefficients and the one fresh
one, [1]'s `(6)`. -/
theorem Zonotope.aux_mem_interHalfspace_iff (Z : Zonotope (Vec ℝ n)) (h : Vec ℝ n →ₗ[ℝ] ℝ)
    (f : ℝ) (x : Vec ℝ n) : -- --- STMT ---
    x ∈ (Z.interHalfspace h f).construct ↔
      ∃ (ξ : Fin Z.h → ℝ) (t : ℝ), (∀ i, |ξ i| ≤ 1) ∧ |t| ≤ 1 ∧
        (∑ i, h (Z.G i) * ξ i) + (f - h Z.c + ∑ i, |h (Z.G i)|) / 2 * t
          = f - h Z.c - (f - h Z.c + ∑ i, |h (Z.G i)|) / 2 ∧
        x = Z.c + ∑ i, ξ i • Z.G i := by -- --- PROOF ---
  show x ∈ (ConZonotope.ofMat Z.c (Fin.append Z.G (fun _ : Fin 1 => (0 : Vec ℝ n)))
      (fun _ : Fin 1 => Fin.append (fun i => h (Z.G i))
        (fun _ : Fin 1 => (f - h Z.c + ∑ i, |h (Z.G i)|) / 2))
      (fun _ : Fin 1 => f - h Z.c - (f - h Z.c + ∑ i, |h (Z.G i)|) / 2)).construct ↔ _
  rw [ConZonotope.mem_ofMat_iff]
  constructor
  -- forward: `ξ`'s two halves, by `castAdd`/`natAdd`, are `Z`'s coefficients and the fresh one
  · rintro ⟨ξ, hξ, hAe, hx⟩
    refine ⟨fun i => ξ (Fin.castAdd 1 i), ξ (Fin.natAdd Z.h 0), fun i => hξ _, hξ _, ?_, ?_⟩
    · rw [← Zonotope.aux_mulVec_interHalfspace]; exact hAe 0
    · rw [hx]; exact Zonotope.aux_value_interHalfspace Z ξ
  -- back: `Fin.append` glues them into the one `ξ` the fresh count asks for
  · rintro ⟨ξ, t, hξ, ht, heq, hx⟩
    refine ⟨Fin.append ξ (fun _ => t),
      Fin.addCases (fun i => by simpa using hξ i) (fun i => by simpa using ht),
      fun i => ?_, ?_⟩
    · have hi0 : i = 0 := Subsingleton.elim i 0
      rw [hi0, Zonotope.aux_mulVec_interHalfspace]
      simpa [Fin.append_left, Fin.append_right] using heq
    · rw [Zonotope.aux_value_interHalfspace]
      simpa [Fin.append_left] using hx

/-- `h`'s value over `Z`'s generators, at any admissible coefficient, never drops below minus the
generators' own total — the triangle inequality both `aux_interHalfspace_dm_nonneg` and the
`⊇`-direction's witness for `t` at `dm = 0` need. -/
theorem Zonotope.aux_sum_ge_neg_sum_abs (Z : Zonotope (Vec ℝ n)) (h : Vec ℝ n →ₗ[ℝ] ℝ)
    (ξ : Fin Z.h → ℝ) (hξ : ∀ i, |ξ i| ≤ 1) :
    -∑ i, |h (Z.G i)| ≤ ∑ i, h (Z.G i) * ξ i := by -- --- PROOF ---
  have hterm : ∀ i ∈ Finset.univ, -|h (Z.G i)| ≤ h (Z.G i) * ξ i := by
    intro i _
    have habs : |h (Z.G i) * ξ i| ≤ |h (Z.G i)| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hξ i)
    linarith [neg_abs_le (h (Z.G i) * ξ i)]
  calc -∑ i, |h (Z.G i)| = ∑ i, -|h (Z.G i)| := by rw [Finset.sum_neg_distrib]
    _ ≤ ∑ i, h (Z.G i) * ξ i := Finset.sum_le_sum hterm

/-- The paper's own first step: `Z` meeting the hyperplane, with the triangle inequality over its
generators, forces `dm ≥ 0`. -/
theorem Zonotope.aux_interHalfspace_dm_nonneg (Z : Zonotope (Vec ℝ n)) (h : Vec ℝ n →ₗ[ℝ] ℝ)
    (f : ℝ) (hZH : ∃ x ∈ Z.construct, h x = f) :
    0 ≤ f - h Z.c + ∑ i, |h (Z.G i)| := by -- --- PROOF ---
  obtain ⟨x, ⟨ξ, hξ, rfl⟩, hx⟩ := hZH
  rw [map_add, map_sum] at hx
  simp only [map_smul, smul_eq_mul] at hx
  have hlo := Zonotope.aux_sum_ge_neg_sum_abs Z h ξ hξ
  have hcomm : ∑ i, ξ i * h (Z.G i) = ∑ i, h (Z.G i) * ξ i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hcomm] at hx
  linarith [hx]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: `Z.interHalfspace h f` denotes exactly `Z ∩ {x | h x ≤ f}`, given that `Z` meets
the hyperplane `{x | h x = f}`. -/
theorem Zonotope.interHalfspace_exact (Z : Zonotope (Vec ℝ n)) (h : Vec ℝ n →ₗ[ℝ] ℝ) (f : ℝ)
    (hZH : ∃ x ∈ Z.construct, h x = f) :
    (Z.interHalfspace h f).construct = Z.construct ∩ {x | h x ≤ f} := by -- --- PROOF ---
  have hdm0 := Zonotope.aux_interHalfspace_dm_nonneg Z h f hZH
  apply Set.eq_of_subset_of_subset
  -- Zh ⊆ Z ∩ H₋: from `(6)` and `t ≥ -1`, `dm ≥ 0` bounds `h (c + Gξ)` above by `f`
  · intro x hx
    obtain ⟨ξ, t, hξ, ht, heq, rfl⟩ := (Zonotope.aux_mem_interHalfspace_iff Z h f _).mp hx
    have htlo := (abs_le.mp ht).1
    refine ⟨⟨ξ, hξ, rfl⟩, ?_⟩
    show h (Z.c + ∑ i, ξ i • Z.G i) ≤ f
    rw [map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
    have hcomm : ∑ i, ξ i * h (Z.G i) = ∑ i, h (Z.G i) * ξ i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hcomm]
    nlinarith [heq, htlo, hdm0]
  -- Z ∩ H₋ ⊆ Zh: witness `t` by the paper's own formula `(7)`, `2/0 = 0` covering `dm = 0`
  · rintro x ⟨⟨ξ, hξ, rfl⟩, hxle⟩
    have hxle' : h Z.c + ∑ i, h (Z.G i) * ξ i ≤ f := by
      have h1 : h (Z.c + ∑ i, ξ i • Z.G i) ≤ f := hxle
      rw [map_add, map_sum] at h1
      simp only [map_smul, smul_eq_mul] at h1
      rwa [Finset.sum_congr rfl (fun i _ => mul_comm (ξ i) (h (Z.G i)))] at h1
    have hSlow := Zonotope.aux_sum_ge_neg_sum_abs Z h ξ hξ
    set S : ℝ := ∑ i, h (Z.G i) * ξ i with hSdef
    set dm : ℝ := f - h Z.c + ∑ i, |h (Z.G i)| with hdmdef
    have hD0 : 0 ≤ f - h Z.c - S := by linarith [hxle']
    have hDdm : f - h Z.c - S ≤ dm := by rw [hdmdef]; linarith [hSlow]
    refine (Zonotope.aux_mem_interHalfspace_iff Z h f _).mpr
      ⟨ξ, 2 / dm * (f - h Z.c - S - dm / 2), hξ, ?_, ?_, rfl⟩
    -- `|t| ≤ 1`: `D := f - h Z.c - S` sits in `[0, dm]`, and `t = 2D/dm - 1`
    · rcases eq_or_lt_of_le hdm0 with hdm0' | hdmpos
      · simp [← hdm0']
      · rw [abs_le, div_mul_eq_mul_div]
        constructor
        · rw [le_div_iff₀ hdmpos]; nlinarith [hD0]
        · rw [div_le_one hdmpos]; nlinarith [hDdm]
    -- `(6)` itself: `D = 0` at `dm = 0`, and clearing the denominator otherwise
    · rcases eq_or_lt_of_le hdm0 with hdm0' | hdmpos
      · have hDeq0 : f - h Z.c - S = 0 := le_antisymm (hDdm.trans_eq hdm0'.symm) hD0
        rw [← hSdef, ← hdm0']
        simp only [zero_div, div_zero, zero_mul]
        linarith [hDeq0]
      · rw [← hSdef]
        field_simp
        ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
