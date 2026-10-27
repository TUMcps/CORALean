module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# A symmetric interval matrix map is `S · box(Z)`

[1, Lemma 3]'s box, whose generators `N̂_j(|c| + Σ|g|)` are what `S · box(Z)` gives.
`Zonotope.mtimesIntervalMat` is already [1, Thm. 4]'s interval-matrix map, and its diagonal
generator block is [1, Lemma 2]'s bound applied to `Z`'s own reach `|c| + Σ|g|` — exactly
`radiusReach`. So at a symmetric matrix, mapping `Z` this way coincides with mapping
`Z.interval.zonotope`, CORA's `S · box(Z)`. At a *symmetric* `IM` (`IM.inf = -IM.sup`),
`IM.center = 0`, which turns the leading generators — the image of `Z`'s own — into an all-zero
block on both sides; `aux_construct_append_zero_left` drops it, and `aux_absBound_interval_zonotope`
is why the diagonal block is the same on both sides.

## Inputs
* `IM` – interval matrix
* `Z` – zonotope

## Hypotheses
* `hIM` – interval symmetric about zero

## Conclusion
* the product with `Z` equals the product with its bounding box

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A leading block of all-zero generators changes nothing a zonotope denotes:
its coefficients are free, and every one of them contributes nothing either
way. -/
private theorem aux_construct_append_zero_left {j k : ℕ} (c : Vec ℝ m)
    (G : Fin k → Vec ℝ m) : -- --- CONCL ---
    (⟨j + k, c, Fin.append (fun _ => (0 : Vec ℝ m)) G⟩ : Zonotope (Vec ℝ m)).construct
      = (⟨k, c, G⟩ : Zonotope (Vec ℝ m)).construct := by -- --- PROOF ---
  ext x
  rw [Zonotope.mem_construct_iff, Zonotope.mem_construct_iff]
  constructor
  · rintro ⟨β, hβ, hx⟩
    refine ⟨fun l => β (Fin.natAdd j l), fun l => hβ _, fun i => ?_⟩
    have h := hx i
    rw [Fin.sum_univ_add] at h
    simpa using h
  · rintro ⟨β, hβ, hx⟩
    refine ⟨Fin.append (fun _ => (0 : ℝ)) β,
      Fin.addCases (fun l => by norm_num) (fun l => by simpa using hβ l), fun i => ?_⟩
    rw [Fin.sum_univ_add]
    simpa using hx i

/-- `Z.interval.zonotope` reaches exactly as far from the origin as `Z` does,
coordinate by coordinate: its one nonzero generator per coordinate is `Z`'s own
reach there, read off `Zonotope.interval`'s width. -/
private theorem aux_absBound_interval_zonotope (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    (Z.interval.zonotope).absBound = Z.absBound := by -- --- PROOF ---
  -- `Zonotope.interval`/`Interval.zonotope` unfold to these by `rfl`
  have hsup : Z.interval.sup = fun i => Z.c i + ∑ k, |Z.G k i| := rfl
  have hinf : Z.interval.inf = fun i => Z.c i - ∑ k, |Z.G k i| := rfl
  funext j
  have hc : (Z.interval.zonotope).c j = Z.c j := by
    show (Z.interval.inf j + Z.interval.sup j) / 2 = Z.c j
    rw [hinf, hsup]; ring
  have hG : ∀ l : Fin n, (Z.interval.zonotope).G l j
      = if j = l then ∑ k, |Z.G k j| else 0 := by
    intro l
    show (if j = l then (Z.interval.sup j - Z.interval.inf j) / 2 else 0)
        = if j = l then ∑ k, |Z.G k j| else 0
    rw [hinf, hsup]
    split_ifs with h
    · ring
    · rfl
  -- only the `l = j` generator is nonzero, so the sum collapses to its one term
  have hsum : ∑ l : Fin n, |(Z.interval.zonotope).G l j| = ∑ k, |Z.G k j| := by
    rw [Finset.sum_eq_single j]
    · rw [hG j, if_pos rfl, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)]
    · intro l _ hl
      rw [hG l, if_neg (Ne.symm hl), abs_zero]
    · intro hc'
      exact absurd (Finset.mem_univ j) hc'
  show |(Z.interval.zonotope).c j| + ∑ l, |(Z.interval.zonotope).G l j|
      = |Z.c j| + ∑ k, |Z.G k j|
  rw [hc]
  congr 1


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimesIntervalMat_symm_box {IM : Interval (Mat ℝ m n)}
    (hIM : IM.inf = -IM.sup) (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    (Zonotope.mtimesIntervalMat IM Z).construct
      = (Zonotope.mtimesIntervalMat IM Z.interval.zonotope).construct := by -- --- PROOF ---
  have hIMc : IM.center = 0 := by
    simp only [Interval.center, hIM, neg_add_cancel, smul_zero]
  have hrad : Zonotope.radiusReach IM Z = Zonotope.radiusReach IM Z.interval.zonotope := by
    funext i
    show (∑ j, IM.radius i j * Z.absBound j)
        = ∑ j, IM.radius i j * (Z.interval.zonotope).absBound j
    rw [aux_absBound_interval_zonotope]
  -- a zero center also zeroes the leading (image-of-`Z`'s-own) generator block
  have hL : Zonotope.mtimesIntervalMat IM Z
      = (⟨Z.h + m, 0, Fin.append (fun _ => (0 : Vec ℝ m))
          (Matrix.diagonal (Zonotope.radiusReach IM Z))⟩ : Zonotope (Vec ℝ m)) := by
    simp only [Zonotope.mtimesIntervalMat, hIMc, Matrix.zero_mulVec]
  have hR : Zonotope.mtimesIntervalMat IM Z.interval.zonotope
      = (⟨Z.interval.zonotope.h + m, 0, Fin.append (fun _ => (0 : Vec ℝ m))
          (Matrix.diagonal (Zonotope.radiusReach IM Z))⟩ : Zonotope (Vec ℝ m)) := by
    simp only [Zonotope.mtimesIntervalMat, hIMc, Matrix.zero_mulVec, ← hrad]
  rw [hL, hR, aux_construct_append_zero_left, aux_construct_append_zero_left]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
