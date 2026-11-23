module

public import CORALean.ContSet.Zonotope.Float.Definitions.ContainsAt
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter

@[expose] public section

/-!
# `Zonotope.mtimes` keeps the weights of the generators

`Zonotope.mtimes` maps the center and each generator one by one and pays its rounding into the
error box, so the image of a point at the weights `β` is a point of the image at the same `β`.

## Inputs
* `M` – matrix
* `Z` – zonotope
* `β` – weights of the generators
* `x` – point

## Hypotheses
* `hx` – `x` is in `Z` at `β`

## Conclusion
* the image of `x` is in the image of `Z` at `β`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   23-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The image of a point at `β` is at `β` in the image: `mtimes` keeps the weights. -/
theorem Zonotope.containsAt_mtimes (M : Mat 𝕋 m n) {Z : Zonotope (Vec 𝕋 n)}
    {β : Vec ℝ Z.h} {x : Vec ℝ n} (hx : Z.ContainsAt β x) : -- --- CONCL ---
    (Zonotope.mtimes M Z).ContainsAt β (toRealMat M *ᵥ x) := by -- --- PROOF ---
  obtain ⟨hβ, e, he, hxe⟩ := hx
  -- the stored generators are wrong by this much, entrywise
  have hgen : ∀ i j, |(∑ k, toReal (M i k) * toReal (Z.G j k))
      - toReal (matMulDown M (fun i j => Z.G j i) i j)|
        ≤ toReal (matMulDiff M (fun i j => Z.G j i) i j) := by
    intro i j
    have hlo : toReal (matMulDown M (fun i j => Z.G j i) i j)
        ≤ ∑ k, toReal (M i k) * toReal (Z.G j k) :=
      dotDown_le (M i) (fun k => Z.G j k)
    have hhi : ∑ k, toReal (M i k) * toReal (Z.G j k)
        ≤ toReal (matMulUp M (fun i j => Z.G j i) i j) :=
      le_dotUp (M i) (fun k => Z.G j k)
    -- the gap of the two roundings bounds the difference
    have hgap := sub_le_subUp (matMulUp M (fun i j => Z.G j i) i j)
      (matMulDown M (fun i j => Z.G j i) i j)
    rw [abs_le]
    exact ⟨by simp only [matMulDiff]; linarith, by simp only [matMulDiff]; linarith⟩
  -- the center's rounding, the generators' rounding and the old box, as boxes
  have hc := Interval.sub_mem_residual (stored := mulVecDown M Z.c)
    (x := fun i => ∑ k, toReal (M i k) * toReal (Z.c k))
    (fun i => ⟨dotDown_le (M i) Z.c, le_dotUp (M i) Z.c⟩)
  have hg := Zonotope.mem_generatorError hgen hβ
  have hMe := Interval.mtimes_outer M Z.I_error ⟨e, he, rfl⟩
  refine ⟨hβ, _, Interval.plus_outer _ _ ⟨_, hMe, _, Interval.plus_outer _ _ ⟨_, hc, _, hg, rfl⟩,
    rfl⟩, fun i => ?_⟩
  -- the exact image, regrouped so the center and each generator appear once
  have hxi : (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G j k)) * β j + (toRealMat M *ᵥ e) i := by
    show ∑ k, toReal (M i k) * x k = _ + _ + ∑ k, toReal (M i k) * e k
    calc ∑ k, toReal (M i k) * x k
        = ∑ k, (toReal (M i k) * toReal (Z.c k)
              + ∑ j, toReal (M i k) * toReal (Z.G j k) * β j + toReal (M i k) * e k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hxe k, mul_add, mul_add, Finset.mul_sum]
          exact congrArg₂ _ (congrArg _ (Finset.sum_congr rfl fun j _ => by ring)) rfl
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm (f := fun k j =>
            toReal (M i k) * toReal (Z.G j k) * β j)]
          congr 2
          exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
  -- a stored generator plus its error is the matrix product's column
  have hsum : (∑ j, toReal (mulVecDown M (Z.G j) i) * β j)
      + (∑ j, (∑ k, toReal (M i k) * toReal (Z.G j k)
          - toReal (matMulDown M (fun i j => Z.G j i) i j)) * β j)
      = ∑ j, (∑ k, toReal (M i k) * toReal (Z.G j k)) * β j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show mulVecDown M (Z.G j) i = matMulDown M (fun i j => Z.G j i) i j from rfl]; ring
  rw [hxi]
  show _ = toReal (mulVecDown M Z.c i) + ∑ j : Fin Z.h, toReal (mulVecDown M (Z.G j) i) * β j
    + ((toRealMat M *ᵥ e) i + (∑ k, toReal (M i k) * toReal (Z.c k) - toReal (mulVecDown M Z.c i)
      + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G j k)
        - toReal (matMulDown M (fun i j => Z.G j i) i j)) * β j))
  linarith [hsum]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
