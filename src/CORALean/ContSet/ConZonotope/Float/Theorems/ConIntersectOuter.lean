module

public import CORALean.ContSet.ConZonotope.Float.Operations.ConIntersect
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.ConZonotope.Float.Theorems.AnchorSlabOuter
public import CORALean.ContSet.HPolytope.Float.Operations.MemSlabNominalIff

@[expose] public section

/-!
# `ConZonotope.conIntersect` over-approximates the constrained intersection

A point `x = y₁ + e₁` of `cZ₁` with `M x = y₂ + e₂` in `cZ₂`, `yₖ` nominal at coefficients `βₖ`
and `eₖ` in its box. The image `M x` is the float image's nominal point at the same `β₁`, `yW`,
plus `eW`: the image of `e₁` and the rounding of `M c₁` and of `M G₁` against `β₁`, all inside
the float image's error box (`Interval.mtimes_outer`, `sub_mem_residual`,
`mem_generatorError`). The agreement row then reads `yW - y₂ = e₂ - eW`, inside its slab, and
`x` is the first set's nominal point at `[β₁; β₂]` plus `e₁` in the slab version, which the
result contains (`ConZonotope.anchorSlab_outer`).

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope
* `M` – map from the first into the second space

## Hypotheses
* none

## Conclusion
* the constrained intersection is contained in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact image of `c + G β + e`, regrouped so the center and each generator appear once. -/
theorem ConZonotope.aux_mulVec_regroup {h : ℕ} (M : Mat 𝕋 m n) (c : Vec 𝕋 n) (G : Fin h → Vec 𝕋 n)
    (β : Vec ℝ h) (e : Vec ℝ n) {x : Vec ℝ n}
    (hx : ∀ k, x k = toReal (c k) + ∑ j, toReal (G j k) * β j + e k) (i : Fin m) : -- --- CONCL ---
    (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (G j k)) * β j
      + (toRealMat M *ᵥ e) i := by -- --- PROOF ---
  show ∑ k, toReal (M i k) * x k = _ + _ + ∑ k, toReal (M i k) * e k
  calc ∑ k, toReal (M i k) * x k
      = ∑ k, (toReal (M i k) * toReal (c k)
              + ∑ j, toReal (M i k) * toReal (G j k) * β j + toReal (M i k) * e k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hx k, mul_add, mul_add, Finset.mul_sum]
        exact congrArg₂ _ (congrArg _ (Finset.sum_congr rfl fun j _ => by ring)) rfl
    _ = (∑ k, toReal (M i k) * toReal (c k))
        + ∑ k, ∑ j, toReal (M i k) * toReal (G j k) * β j
        + ∑ k, toReal (M i k) * e k := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = _ := by
        rw [Finset.sum_comm (f := fun k j => toReal (M i k) * toReal (G j k) * β j)]
        exact congrArg₂ _ (congrArg _ (Finset.sum_congr rfl fun j _ =>
          (Finset.sum_mul _ _ _).symm)) rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.conIntersect_outer (cZ₁ : ConZonotope 𝕋 (Vec 𝕋 n))
    (cZ₂ : ConZonotope 𝕋 (Vec 𝕋 m))
    (M : Mat 𝕋 m n) : -- --- CONCL ---
    {x | x ∈ cZ₁.construct ∧ toRealMat M *ᵥ x ∈ cZ₂.construct}
      ⊆ (cZ₁.conIntersect cZ₂ M).construct := by -- --- PROOF ---
  intro x hx
  -- the rows as a slab first, which `anchorSlab` contains
  refine ConZonotope.anchorSlab_outer _ _ _ _ ?_
  obtain ⟨⟨y₁, hy₁', e₁, he₁, hx₁⟩, y₂, hy₂', e₂, he₂, hx₂⟩ := hx
  obtain ⟨β₁, hβ₁, hP₁, hy₁⟩ := ConZonotope.mem_nominalSet_iff.mp hy₁'
  obtain ⟨β₂, hβ₂, hP₂, hy₂⟩ := ConZonotope.mem_nominalSet_iff.mp hy₂'
  set W := Zonotope.mtimes M ⟨cZ₁.h, cZ₁.c, fun j i => cZ₁.G j i, cZ₁.I_error⟩ with hW
  -- the float image's nominal point at `β₁`, and what is left of `M x`
  set yW : Vec ℝ m := fun i => toReal (W.c i) + ∑ j, toReal (W.G j i) * β₁ j with hyW
  set eW : Vec ℝ m := fun i => (toRealMat M *ᵥ x) i - yW i with heW
  have hxk : ∀ k, x k = toReal (cZ₁.c k) + ∑ j, toReal (cZ₁.G j k) * β₁ j + e₁ k := by
    intro k
    have h := congrFun hx₁ k
    simp only at h
    rw [← h, Pi.add_apply, hy₁ k]
  -- the rest lies in the float image's error box
  have heWmem : eW ∈ W.I_error.construct := by
    -- the generators are wrong by this much, entrywise
    have hgen : ∀ i j, |(∑ k, toReal (M i k) * toReal (cZ₁.G j k))
        - toReal (mulVecDown M (cZ₁.G j) i)|
          ≤ toReal (matMulDiff M (fun i j => cZ₁.G j i) i j) := by
      intro i j
      have hlo : toReal (mulVecDown M (cZ₁.G j) i) ≤ ∑ k, toReal (M i k) * toReal (cZ₁.G j k) :=
        dotDown_le (M i) (fun k => cZ₁.G j k)
      have hhi : ∑ k, toReal (M i k) * toReal (cZ₁.G j k) ≤ toReal (mulVecUp M (cZ₁.G j) i) :=
        le_dotUp (M i) (fun k => cZ₁.G j k)
      have hgap := sub_le_subUp (mulVecUp M (cZ₁.G j) i) (mulVecDown M (cZ₁.G j) i)
      change _ ≤ toReal (subUp (mulVecUp M (cZ₁.G j) i) (mulVecDown M (cZ₁.G j) i))
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    -- the box's image, then the center's and the generators' rounding
    refine Interval.plus_outer _ _
        ⟨toRealMat M *ᵥ e₁, Interval.mtimes_outer M cZ₁.I_error ⟨e₁, he₁, rfl⟩,
      _, Interval.plus_outer _ _
        ⟨_, Interval.sub_mem_residual (stored := mulVecDown M cZ₁.c)
            (fun i => ⟨dotDown_le (M i) cZ₁.c, le_dotUp (M i) cZ₁.c⟩),
         _, Zonotope.mem_generatorError hgen hβ₁, rfl⟩, ?_⟩
    -- the stored generators and their errors recombine into the exact image
    funext i
    have hsum : (∑ j, toReal (mulVecDown M (cZ₁.G j) i) * β₁ j)
        + (∑ j, (∑ k, toReal (M i k) * toReal (cZ₁.G j k)
            - toReal (mulVecDown M (cZ₁.G j) i)) * β₁ j)
        = ∑ j, (∑ k, toReal (M i k) * toReal (cZ₁.G j k)) * β₁ j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    show (toRealMat M *ᵥ e₁) i
        + ((∑ k, toReal (M i k) * toReal (cZ₁.c k) - toReal (mulVecDown M cZ₁.c i))
          + ∑ j, (∑ k, toReal (M i k) * toReal (cZ₁.G j k)
              - toReal (mulVecDown M (cZ₁.G j) i)) * β₁ j)
      = (toRealMat M *ᵥ x) i - (toReal (mulVecDown M cZ₁.c i)
          + ∑ j, toReal (mulVecDown M (cZ₁.G j) i) * β₁ j)
    rw [ConZonotope.aux_mulVec_regroup M cZ₁.c cZ₁.G β₁ e₁ hxk i]
    linarith [hsum]
  -- the witness: the first set's nominal point at `[β₁; β₂]`, with its own box point
  have hx₂' : ∀ i, y₂ i + e₂ i = (toRealMat M *ᵥ x) i := fun i => congrFun hx₂ i
  refine ⟨y₁, ConZonotope.mem_nominalSet_iff.mpr ⟨Fin.append β₁ β₂, ?_, ?_, ?_⟩, e₁, he₁, hx₁⟩
  · refine Fin.addCases (fun l => ?_) fun l => ?_
    · rw [Fin.append_left]; exact hβ₁ l
    · rw [Fin.append_right]; exact hβ₂ l
  -- each half its own constraints, then the agreement rows
  · refine HPolytope.mem_stackRows_nominal_iff.mpr
      ⟨HPolytope.mem_stackRows_nominal_iff.mpr ⟨HPolytope.mem_padLeft_nominal_iff.mpr ?_,
        HPolytope.mem_padRight_nominal_iff.mpr ?_⟩, HPolytope.mem_slab_nominal_iff.mpr fun i => ?_⟩
    · rw [blockLeft_append]; exact hP₁
    · rw [blockRight_append]; exact hP₂
    -- the agreement row: the two nominal points differ by exactly `e₂ - eW`
    · have hrow : (toRealMat (fun i => Fin.append (fun j => W.G j i) fun j => neg (cZ₂.G j i))
            *ᵥ Fin.append β₁ β₂) i
          = (yW i - toReal (W.c i)) - (y₂ i - toReal (cZ₂.c i)) := by
        rw [hy₂ i]
        simp only [hyW, mulVec, dotProduct, toRealMat, Fin.sum_univ_add, Fin.append_left,
          Fin.append_right, toReal_neg, neg_mul, Finset.sum_neg_distrib]
        ring
      have hbW : toReal (W.I_error.inf i) ≤ eW i ∧ eW i ≤ toReal (W.I_error.sup i) := heWmem i
      have hb₂ : toReal (cZ₂.I_error.inf i) ≤ e₂ i ∧ e₂ i ≤ toReal (cZ₂.I_error.sup i) := he₂ i
      have hxi : yW i + eW i = y₂ i + e₂ i := by
        rw [hx₂' i, heW]; ring
      -- both ends: the stored bound rounded outward from the extreme `e₂ - eW`
      refine ⟨?_, ?_⟩
      · show toReal (addDown (subDown (cZ₂.c i) (W.c i))
            (subDown (cZ₂.I_error.inf i) (W.I_error.sup i))) ≤ _
        refine le_of_le_of_eq ?_ hrow.symm
        linarith [addDown_le_add (subDown (cZ₂.c i) (W.c i))
            (subDown (cZ₂.I_error.inf i) (W.I_error.sup i)),
          subDown_le_sub (cZ₂.c i) (W.c i),
          subDown_le_sub (cZ₂.I_error.inf i) (W.I_error.sup i), hbW.2, hb₂.1]
      · show _ ≤ toReal (addUp (subUp (cZ₂.c i) (W.c i))
            (subUp (cZ₂.I_error.sup i) (W.I_error.inf i)))
        refine le_of_eq_of_le hrow ?_
        linarith [add_le_addUp (subUp (cZ₂.c i) (W.c i))
            (subUp (cZ₂.I_error.sup i) (W.I_error.inf i)),
          sub_le_subUp (cZ₂.c i) (W.c i),
          sub_le_subUp (cZ₂.I_error.sup i) (W.I_error.inf i), hbW.1, hb₂.2]
  -- the second generator block is zero, so the point is the first operand's
  · intro i
    rw [hy₁ i]
    show _ = toReal (cZ₁.c i)
      + ∑ j : Fin (cZ₁.h + cZ₂.h),
          toReal (Fin.append cZ₁.G (fun _ _ => (zero : 𝕋)) j i) * Fin.append β₁ β₂ j
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, toReal_zero, zero_mul,
      Finset.sum_const_zero, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
