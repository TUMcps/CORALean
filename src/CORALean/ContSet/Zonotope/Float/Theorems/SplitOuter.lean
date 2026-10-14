module

public import CORALean.ContSet.InflatedContSet.InflatedContSet
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Zonotope.Float.Operations.Split
public import CORALean.ContSet.Zonotope.Float.Operations.SplitHalf
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Real.Theorems.SplitUnion

@[expose] public section

/-!
# The halves of `Zonotope.split` cover the zonotope, over a floating-point scalar

The nominal part is the exact layer's `split_union` at the nominal zonotope. A real half
differs from the stored half only in its centre, by the rounding of `c ∓ g_j/2`; that
difference lies in the `centerResidual`, which the half's box has absorbed. The generators
match entry by entry, the halved one because halving is exact (`toReal_half`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of a real half, its centre read off with the shift `s`, plus a point of the box,
lies in the stored half: same coefficients, and the centre rounding in the box. -/
theorem Zonotope.aux_splitHalf_mem (Z : Zonotope (Vec 𝕋 n)) (j : Fin Z.h) (s : Vec 𝕋 n)
    {zn e : Vec ℝ n}
    (he : e ∈ Z.I_error.construct) (β : Vec ℝ Z.h) (hβ : ∀ k, |β k| ≤ 1)
    (hzn : ∀ i, zn i = toReal (Z.c i) + toReal (s i)
      + ∑ k, β k * Function.update (fun k => toReal (Z.G k i)) j (toReal (Z.G j i) / 2) k) :
    zn + e ∈ (Z.splitHalf j s).construct := by -- --- PROOF ---
  -- the stored generators read as the real halved ones, entry by entry
  have hG : ∀ (i : Fin n) (k : Fin Z.h), toReal ((Z.splitHalf j s).G k i)
      = Function.update (fun k => toReal (Z.G k i)) j (toReal (Z.G j i) / 2) k := by
    intro i k
    by_cases hk : k = j
    · subst hk
      show toReal (Function.update Z.G k (fun i => half (Z.G k i)) k i) = _
      simp only [Function.update_self, toReal_half]
    · show toReal (Function.update Z.G j (fun i => half (Z.G j i)) k i) = _
      rw [Function.update_of_ne hk, Function.update_of_ne hk]
  have hr := Interval.sub_mem_residual (stored := fun i => addDown (Z.c i) (s i))
    (lo := fun i => addDown (Z.c i) (s i)) (hi := fun i => addUp (Z.c i) (s i))
    (x := fun i => toReal (Z.c i) + toReal (s i))
    fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩
  -- the box point is the incoming one plus the centre rounding, inside the plus of the boxes
  refine ⟨fun i => toReal ((Z.splitHalf j s).c i)
            + ∑ k, toReal ((Z.splitHalf j s).G k i) * β k,
    Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun _ => rfl⟩, _,
    Interval.plus_outer Z.I_error (Zonotope.centerResidual Z.c s) ⟨e, he, _, hr, rfl⟩, ?_⟩
  -- compare coordinate by coordinate: the stored sum reads as the real halved one
  funext i
  have hs : ∑ k, toReal ((Z.splitHalf j s).G k i) * β k
      = ∑ k, β k * Function.update (fun k => toReal (Z.G k i)) j (toReal (Z.G j i) / 2) k :=
    Finset.sum_congr rfl fun k _ => by rw [hG, mul_comm]
  have hc : (Z.splitHalf j s).c i = addDown (Z.c i) (s i) := rfl
  simp only [Pi.add_apply, hc, hs, hzn i]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.split_outer (Z : Zonotope (Vec 𝕋 n)) (j : Fin Z.h) :
    Z.construct ⊆ (Z.split j).1.construct ∪ (Z.split j).2.construct := by -- --- PROOF ---
  rintro _ ⟨zn, hzn, e, he, rfl⟩
  -- the nominal point lies in one of the real halves
  have hmem : zn ∈ ((nominal Z).split j).1.construct ∪ ((nominal Z).split j).2.construct :=
    (Real.Zonotope.split_union (nominal Z) j).symm ▸ hzn
  -- the real halved generators, read entry by entry
  have key : ∀ (i : Fin n) (k : Fin Z.h),
      Function.update (nominal Z).G j ((2 : ℝ)⁻¹ • (nominal Z).G j) k i
        = Function.update (fun k => toReal (Z.G k i)) j (toReal (Z.G j i) / 2) k := by
    intro i k
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self, Function.update_self]
      show 2⁻¹ * toReal (Z.G k i) = toReal (Z.G k i) / 2
      ring
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]; rfl
  rcases hmem with ⟨β, hβ, hx⟩ | ⟨β, hβ, hx⟩
  -- first half, centre `c - g_j/2`
  · refine Or.inl (Zonotope.aux_splitHalf_mem Z j _ he β hβ fun i => ?_)
    have hx' : zn = ((nominal Z).c - (2 : ℝ)⁻¹ • (nominal Z).G j)
        + ∑ k, β k • Function.update (nominal Z).G j ((2 : ℝ)⁻¹ • (nominal Z).G j) k := hx
    -- read the equation at coordinate `i`, the stored entries as `toReal`
    have h := congrFun hx' i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, key]
      at h
    rw [show (nominal Z).c i = toReal (Z.c i) from rfl,
      show (nominal Z).G j i = toReal (Z.G j i) from rfl] at h
    rw [h]
    congr 1
    rw [toReal_neg, toReal_half]
    ring
  -- second half, centre `c + g_j/2`
  · refine Or.inr (Zonotope.aux_splitHalf_mem Z j _ he β hβ fun i => ?_)
    have hx' : zn = ((nominal Z).c + (2 : ℝ)⁻¹ • (nominal Z).G j)
        + ∑ k, β k • Function.update (nominal Z).G j ((2 : ℝ)⁻¹ • (nominal Z).G j) k := hx
    -- read the equation at coordinate `i`, the stored entries as `toReal`
    have h := congrFun hx' i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, key] at h
    rw [show (nominal Z).c i = toReal (Z.c i) from rfl,
      show (nominal Z).G j i = toReal (Z.G j i) from rfl] at h
    rw [h]
    congr 1
    rw [toReal_half]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
