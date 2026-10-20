module

public import CORALean.ContSet.ConZonotope.Real.Operations.Enclose
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Convex
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# `ConZonotope.enclose` encloses every segment, when the constraints agree

Not exact: even with `hP`, the construction gives every generator's block a symmetric `[-1,1]`
weight, while the true segment ties the two sides' weights to a single `a ∈ [0,1]`, as a zonotope's
`enclose` already loses. `hP` reads `cZ₂.P` back at `cZ₁`'s index, and `HPolytope.convex_construct`
turns the two sides' membership in the *same* polytope into membership of their convex combination.
The value equation reindexes `cZ₂`'s sum by `Fin.castOrderIso`, as `Zonotope.minkDiffAligned_inner`
does.

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope

## Hypotheses
* `hh` – both have the same generator count
* `hP` – the constraints agree

## Conclusion
* the segments between the two sets are contained in the result
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A convex combination of two coefficients each bounded by `1` stays bounded
by `1` — the bound `enclose`'s average block needs. -/
theorem ConZonotope.aux_abs_convComb_le_one {lam p q : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) : -- --- CONCL ---
    |lam * p + (1 - lam) * q| ≤ 1 := by -- --- PROOF ---
  have hm0 : (0:ℝ) ≤ 1 - lam := by linarith
  calc |lam * p + (1 - lam) * q| ≤ |lam * p| + |(1 - lam) * q| := abs_add_le _ _
    _ = lam * |p| + (1 - lam) * |q| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hl0, abs_of_nonneg hm0]
    _ ≤ lam * 1 + (1 - lam) * 1 := by gcongr
    _ = 1 := by ring

/-- The same bound with a difference instead of a sum — `enclose`'s other
fresh block. -/
theorem ConZonotope.aux_abs_convComb_sub_le_one {lam p q : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) : -- --- CONCL ---
    |lam * p - (1 - lam) * q| ≤ 1 := by -- --- PROOF ---
  have hm0 : (0:ℝ) ≤ 1 - lam := by linarith
  rw [sub_eq_add_neg]
  calc |lam * p + -((1 - lam) * q)| ≤ |lam * p| + |-((1 - lam) * q)| := abs_add_le _ _
    _ = lam * |p| + (1 - lam) * |q| := by
        rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hl0, abs_of_nonneg hm0]
    _ ≤ lam * 1 + (1 - lam) * 1 := by gcongr
    _ = 1 := by ring

/-- The restatement `Fin.sum_univ_add` needs: `enclose`'s generator count is not
syntactically `cZ₁.h + cZ₁.h + 1` until this unfolds it. -/
theorem ConZonotope.aux_sum_univ_enclose {M : Type} [AddCommMonoid M] {cZ₁ cZ₂ : ConZonotope α}
    {hh : cZ₁.h = cZ₂.h} (f : Fin (cZ₁.h + cZ₁.h + 1) → M) :
    ∑ j : Fin (cZ₁.enclose cZ₂ hh).h, f j
      = ∑ i : Fin (cZ₁.h + cZ₁.h), f (Fin.castAdd 1 i)
        + ∑ i : Fin 1, f (Fin.natAdd (cZ₁.h + cZ₁.h) i) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.enclose_outer (cZ₁ cZ₂ : ConZonotope α) (hh : cZ₁.h = cZ₂.h)
    (hP : cZ₂.P = cZ₁.P.comap (reindexLin (Fin.castOrderIso hh).toEquiv)) : -- --- CONCL ---
    Set.linComb cZ₁.construct cZ₂.construct ⊆ (cZ₁.enclose cZ₂ hh).construct := by -- --- PROOF ---
  rintro x ⟨y₁, ⟨β₁, hβ₁, hP₁, rfl⟩, y₂, ⟨β₂, hβ₂, hP₂, rfl⟩, lam, ⟨hl0, hl1⟩, rfl⟩
  have hm0 : (0:ℝ) ≤ 1 - lam := by linarith
  -- `β₂` read at `cZ₁`'s index lies in `cZ₁.P` too, the two sharing one system
  have hβ₂' : (fun j => β₂ (Fin.cast hh j)) ∈ cZ₁.P.construct := by
    have h2 : β₂ ∈ (cZ₁.P.comap (reindexLin (Fin.castOrderIso hh).toEquiv)).construct := hP ▸ hP₂
    rwa [HPolytope.comap_exact] at h2
  set β₂' : Fin cZ₁.h → ℝ := fun j => β₂ (Fin.cast hh j) with hβ₂'def
  set s : Fin cZ₁.h → ℝ := fun j => lam * β₁ j + (1 - lam) * β₂' j with hsdef
  set u : Fin cZ₁.h → ℝ := fun j => lam * β₁ j - (1 - lam) * β₂' j with hudef
  refine ⟨Fin.append (Fin.append s u) (fun _ : Fin 1 => 2 * lam - 1), ?_, ?_, ?_⟩
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro j
        simp only [Fin.append_left]
        exact ConZonotope.aux_abs_convComb_le_one hl0 hl1 (hβ₁ j) (hβ₂ (Fin.cast hh j))
      · intro j
        simp only [Fin.append_left, Fin.append_right]
        exact ConZonotope.aux_abs_convComb_sub_le_one hl0 hl1 (hβ₁ j) (hβ₂ (Fin.cast hh j))
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]; constructor <;> linarith
  -- the coefficient block: `blockLeft` twice recovers `s`, and convexity does the rest
  · show Fin.append (Fin.append s u) (fun _ : Fin 1 => 2 * lam - 1)
        ∈ (cZ₁.P.comap ((blockLeft cZ₁.h cZ₁.h).comp (blockLeft (cZ₁.h + cZ₁.h) 1))).construct
    rw [HPolytope.comap_exact, Set.mem_preimage, LinearMap.comp_apply]
    have hproj : blockLeft (cZ₁.h + cZ₁.h) 1
        (Fin.append (Fin.append s u) (fun _ : Fin 1 => 2 * lam - 1)) = Fin.append s u :=
      blockLeft_append _ _
    rw [hproj, blockLeft_append]
    have hconv := (HPolytope.convex_construct cZ₁.P) hP₁ hβ₂' hl0 hm0
      (show lam + (1 - lam) = 1 by ring)
    have hseq : s = lam • β₁ + (1 - lam) • β₂' := by
      funext j; simp [hsdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rwa [hseq]
  -- the value: reindex `cZ₂`'s sum onto `cZ₁`'s count, then match the three blocks
  · have hs₁ : ∑ j : Fin cZ₁.h, (lam * β₁ j) • cZ₁.G j = lam • ∑ j, β₁ j • cZ₁.G j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_smul lam (β₁ j) (cZ₁.G j)
    have hs₂ : ∑ j : Fin cZ₁.h, ((1 - lam) * β₂' j) • cZ₂.G (Fin.cast hh j)
        = (1 - lam) • ∑ j, β₂' j • cZ₂.G (Fin.cast hh j) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_smul (1 - lam) (β₂' j) (cZ₂.G (Fin.cast hh j))
    have hsum2 : ∑ k : Fin cZ₂.h, β₂ k • cZ₂.G k
        = ∑ j : Fin cZ₁.h, β₂' j • cZ₂.G (Fin.cast hh j) :=
      (Equiv.sum_comp (Fin.castOrderIso hh).toEquiv (fun k => β₂ k • cZ₂.G k)).symm
    -- what one index of the average and half-difference blocks give back together
    have hterm : ∀ j : Fin cZ₁.h,
        s j • ((2:ℝ)⁻¹ • (cZ₁.G j + cZ₂.G (Fin.cast hh j)))
          + u j • ((2:ℝ)⁻¹ • (cZ₁.G j - cZ₂.G (Fin.cast hh j)))
          = (lam * β₁ j) • cZ₁.G j + ((1 - lam) * β₂' j) • cZ₂.G (Fin.cast hh j) := by
      intro j
      rw [hsdef, hudef]
      module
    rw [hsum2, ConZonotope.aux_sum_univ_enclose (hh := hh), Fin.sum_univ_add, Fin.sum_univ_one]
    simp only [ConZonotope.enclose, Fin.append_left, Fin.append_right]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ => hterm j,
      Finset.sum_add_distrib, hs₁, hs₂]
    module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
