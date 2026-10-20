module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Zonotope.Real.Operations.EnclGenSel

@[expose] public section

/-!
# [1, Alg. 1] never leaves the minuend

`Z_{m,encl}` is built from the minuend's own generators at the minuend's own center, so whatever
the sort, the threshold and the containment oracle do, the result stays inside `Z_m` — the
coefficients of the generators left out are zero. That makes [1, Prop. 4]'s split a split. The
other half of [1, Alg. 1]'s intent, `Z_{m,encl} ⊇ Z_s`, is *not* proved here and cannot be:
line 11's test is the caller's `encloses`, the loop may also leave by exhausting `ξ < n_m`, and the
paper itself says the difference is empty when no `ξ` works. A caller that needs the enclosure has
to read it off its own oracle.

## Inputs
* `le` – decidable non-strict comparison
* `lt` – decidable strict comparison
* `encloses` – enclosure test
* `Zm` – zonotope to select from
* `Zs` – zonotope to enclose
* `μbar` – ratio threshold

## Hypotheses
* none

## Conclusion
* the selected part lies in `Zm`

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Dropping generators only shrinks: the ones left out get coefficient zero. -/
theorem aux_genSelection_subset {α : Type} [AddCommGroup α] [Module ℝ α]
    (Z : Zonotope α) (σ : Equiv.Perm (Fin Z.h)) (ξ : ℕ) : -- --- CONCL ---
    (Z.aux_genSelection σ Z.c ξ).construct ⊆ Z.construct := by -- --- PROOF ---
  rintro x ⟨β, hβ, rfl⟩
  set f : Fin (min ξ Z.h) → Fin Z.h :=
    fun i => σ (Fin.castLE (min_le_right ξ Z.h) i) with hf
  have hfinj : Function.Injective f := fun a b hab => by
    have := σ.injective hab
    exact Fin.ext (by simpa [Fin.castLE] using congrArg Fin.val this)
  refine ⟨Function.extend f β (fun _ => (0:ℝ)), fun k => ?_, ?_⟩
  · by_cases hk : ∃ i, f i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [hfinj.extend_apply]
      exact hβ i
    · rw [Function.extend_apply' _ _ _ hk]
      simp
  · -- every index outside the selection contributes nothing
    have hzero : ∀ k ∈ (Finset.univ : Finset (Fin Z.h)), k ∉ Finset.univ.image f →
        Function.extend f β (fun _ => (0:ℝ)) k • Z.G k = 0 := by
      intro k _ hk
      rw [Function.extend_apply' _ _ _ (by simpa using hk), zero_smul]
    have himg : ∑ k ∈ Finset.univ.image f, Function.extend f β (fun _ => (0:ℝ)) k • Z.G k
        = ∑ i, β i • Z.G (f i) :=
      (Finset.sum_image fun a _ b _ h => hfinj h).trans
        (Finset.sum_congr rfl fun i _ => by rw [hfinj.extend_apply])
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero, himg]
    rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]'s `Z_{m,encl}` is a part of the minuend, whatever the oracle. -/
theorem Zonotope.enclGenSel_subset (le lt : ℝ → ℝ → Bool)
    (encloses : Zonotope (Vec ℝ n) → Bool) (Zm Zs : Zonotope (Vec ℝ n)) (μbar : ℝ) :
    (Zm.enclGenSel le lt encloses Zs μbar).construct ⊆ Zm.construct :=
  aux_genSelection_subset Zm _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
