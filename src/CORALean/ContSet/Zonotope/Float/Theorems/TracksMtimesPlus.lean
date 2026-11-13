module

public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Zonotope.Float.Definitions.Tracks
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.MemToSetIffContainsAt
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

@[expose] public section

/-!
# A linear map plus a box keeps the generators in front

`Zonotope.mtimes` maps the generators and the center one by one and pays its rounding into the
error box, so a point at the weights `β` is mapped to a point at the same `β`. `Zonotope.plus`
puts the generators of its second operand after those of the first. The box of a layer is added
as the zonotope of that box, so a map that is a linear map plus a point of the box at each point
of `X` is tracked by `(X.mtimes M).plus B.zonotope`, with the weights of `X` unchanged.

## Inputs
* `M` – matrix
* `B` – box
* `X` – zonotope
* `f` – map

## Hypotheses
* `hf` – the map differs from the linear map by a point of the box, on every point of `X`

## Conclusion
* the sum of the image and the box tracks the map over the zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The image of a point at `β` is at `β` in the image: `mtimes` keeps the weights. -/
private theorem Zonotope.aux_containsAt_mtimes (M : Mat 𝕋 m n) {Z : Zonotope (Vec 𝕋 n)}
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

/-- The sum of points at `β₁` and `β₂` is at the weights side by side in the sum. -/
private theorem Zonotope.aux_containsAt_plus {Z₁ Z₂ : Zonotope (Vec 𝕋 n)} {β₁ : Vec ℝ Z₁.h}
    {β₂ : Vec ℝ Z₂.h} {x₁ x₂ : Vec ℝ n} (h₁ : Z₁.ContainsAt β₁ x₁)
    (h₂ : Z₂.ContainsAt β₂ x₂) : -- --- CONCL ---
    (Z₁.plus Z₂).ContainsAt (Fin.append β₁ β₂) (x₁ + x₂) := by -- --- PROOF ---
  obtain ⟨hβ₁, e₁, he₁, hx₁⟩ := h₁
  obtain ⟨hβ₂, e₂, he₂, hx₂⟩ := h₂
  -- the stored center is below the exact sum, by this much
  have hr := Interval.sub_mem_residual (stored := fun i => addDown (Z₁.c i) (Z₂.c i))
    (x := fun i => toReal (Z₁.c i) + toReal (Z₂.c i))
    (lo := fun i => addDown (Z₁.c i) (Z₂.c i)) (hi := fun i => addUp (Z₁.c i) (Z₂.c i))
    (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩)
  refine ⟨?_, _, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨e₁, he₁, e₂, he₂, rfl⟩,
    _, hr, rfl⟩, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun l => ?_)
    · simpa using hβ₁ l
    · simpa using hβ₂ l
  · show _ = toReal (addDown (Z₁.c i) (Z₂.c i)) + ∑ j : Fin (Z₁.h + Z₂.h),
      toReal (Fin.append Z₁.G Z₂.G j i) * Fin.append β₁ β₂ j + _
    rw [Fin.sum_univ_add]
    simp only [Pi.add_apply, hx₁ i, hx₂ i, Fin.append_left, Fin.append_right]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.tracks_mtimes_plus (M : Mat 𝕋 m n) (B : Interval (Vec 𝕋 m))
    (X : Zonotope (Vec 𝕋 n)) {f : Vec ℝ n → Vec ℝ m}
    (hf : ∀ x ∈ X.toSet, (fun i => f x i - (toRealMat M *ᵥ x) i) ∈ B.toSet) : -- --- CONCL ---
    X.Tracks ((Zonotope.mtimes M X).plus B.zonotope) f := by -- --- PROOF ---
  refine ⟨Nat.le_add_right _ _, fun β x hx => ?_⟩
  -- the box point, at weights of the box's zonotope
  obtain ⟨γ, hγ⟩ := Zonotope.mem_toSet_iff_containsAt.mp
    (Interval.zonotope_contains B (hf x (Zonotope.mem_toSet_iff_containsAt.mpr ⟨β, hx⟩)))
  refine ⟨Fin.append β γ, fun j => Fin.append_left β γ j, ?_⟩
  convert Zonotope.aux_containsAt_plus (Zonotope.aux_containsAt_mtimes M hx) hγ using 1
  funext i
  simp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
