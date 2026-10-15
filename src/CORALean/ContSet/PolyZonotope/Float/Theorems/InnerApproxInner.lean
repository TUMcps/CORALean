module

public import CORALean.ContSet.Interval.Float.Theorems.LeSound
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerApprox
public import CORALean.ContSet.PolyZonotope.Float.Theorems.InnerApproxImageSubsetImage
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `innerApprox` is an inner approximation

Every zonotope `innerApprox` returns lies in the polynomial zonotope. Its box part lies in the
box it was made from, the center being in the box and the radii no larger than the distances to
the bounds; that box is inside the image of the factor cube under the dependent point map
(`innerApproxImage_subset_image`); the independent generators are the set's own, and the error
box holds `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.innerApprox_inner (pZ : PolyZonotope (Vec 𝕋 n)) (tol : 𝕋)
    (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter depth : ℕ) :
    ∀ Z ∈ PolyZonotope.innerApprox pZ tol inv iter depth,
      Z.construct ⊆ pZ.construct := by -- --- PROOF ---
  intro Z hZ z hz
  unfold PolyZonotope.innerApprox at hZ
  dsimp only at hZ
  split at hZ
  case isFalse => cases hZ
  rename_i herr
  obtain ⟨Y, hYS, hYZ⟩ := List.mem_filterMap.mp hZ
  split at hYZ
  case isFalse => cases hYZ
  rename_i hc
  cases hYZ
  obtain ⟨z₀, hz₀, e, he, rfl⟩ := hz
  -- the error box of the result is `0`
  have he0 : e = 0 := funext fun i => le_antisymm
    (le_of_le_of_eq (he i).2 (toReal_zero (𝕋 := 𝕋)))
    (le_of_eq_of_le (toReal_zero (𝕋 := 𝕋)).symm (he i).1)
  -- the center and the radii of the zonotope made from `Y`
  set c : Vec 𝕋 n := Interval.center Y
  set r : Vec 𝕋 n := fun i => maximum zero (minimum (subDown (Y.sup i) (c i))
    (subDown (c i) (Y.inf i)))
  obtain ⟨β, hβ, hz₀⟩ := Zonotope.mem_nominalSet_iff.mp hz₀
  -- the box part `c + r β` lies in `Y`
  set w : Vec ℝ n := fun i => toReal (c i) + toReal (r i) * β (Fin.castAdd pZ.q i)
  have hw : w ∈ Y.construct := by
    intro i
    have hci := Interval.le_subset hc (Interval.mem_point c) i
    have hci1 : toReal (Y.inf i) ≤ toReal (c i) := hci.1
    have hci2 : toReal (c i) ≤ toReal (Y.sup i) := hci.2
    have h1 := subDown_le_sub (Y.sup i) (c i)
    have h2 := subDown_le_sub (c i) (Y.inf i)
    have hr : toReal (r i) = max 0 (min (toReal (subDown (Y.sup i) (c i)))
        (toReal (subDown (c i) (Y.inf i)))) := by
      simp only [r, toReal_maximum, toReal_minimum, toReal_zero]
    -- `0 ≤ r ≤ min(sup - c, c - inf)`
    have hr0 : 0 ≤ toReal (r i) := hr ▸ le_max_left _ _
    have hr1 : toReal (r i) ≤ toReal (Y.sup i) - toReal (c i) := by
      rw [hr]; exact max_le (by linarith) (le_trans (min_le_left _ _) h1)
    have hr2 : toReal (r i) ≤ toReal (c i) - toReal (Y.inf i) := by
      rw [hr]; exact max_le (by linarith) (le_trans (min_le_right _ _) h2)
    have hb := abs_le.mp (hβ (Fin.castAdd pZ.q i))
    have hm1 : -toReal (r i) ≤ toReal (r i) * β (Fin.castAdd pZ.q i) := by nlinarith
    have hm2 : toReal (r i) * β (Fin.castAdd pZ.q i) ≤ toReal (r i) := by nlinarith
    show toReal (Y.inf i) ≤ toReal (c i) + toReal (r i) * β (Fin.castAdd pZ.q i) ∧
      toReal (c i) + toReal (r i) * β (Fin.castAdd pZ.q i) ≤ toReal (Y.sup i)
    exact ⟨by linarith, by linarith⟩
  obtain ⟨a, ha, hwa⟩ := PolyZonotope.innerApproxImage_subset_image pZ _ tol inv iter depth _ Y
    hYS hw
  -- `z₀` is the dependent point at `a` plus the independent generators at `β`'s tail
  refine ⟨z₀, PolyZonotope.mem_nominalSet_iff.mpr ⟨a, fun j => β (Fin.natAdd n j),
    fun k => abs_le.mpr ⟨?_, ?_⟩, fun j => hβ _, fun i => ?_⟩, e, ?_, by rw [he0]⟩
  · have h : toReal (neg one : 𝕋) ≤ a k := (ha k).1
    rw [toReal_neg, toReal_one] at h
    exact h
  · have h : a k ≤ toReal (one : 𝕋) := (ha k).2
    rw [toReal_one] at h
    exact h
  · rw [hz₀ i, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    -- the diagonal block reads the coordinate `i` alone
    have hdiag : ∑ j : Fin n, toReal (if i = j then r j else zero) * β (Fin.castAdd pZ.q j)
        = toReal (r i) * β (Fin.castAdd pZ.q i) := by
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), toReal_zero,
        zero_mul]) (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
    have hwi := congrFun hwa i
    simp only [w, Real.PolyZonotope.point, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hwi
    rw [hdiag, ← add_assoc, ← hwi]
    simp only [mul_comm]
    rfl
  · -- `0` is in the error box
    rw [he0]
    intro i
    have h := List.all_eq_true.mp herr i (List.mem_finRange i)
    simp only [Bool.and_eq_true] at h
    exact ⟨le_of_le_of_eq (toReal_le_of_le h.1) toReal_zero,
      le_of_eq_of_le toReal_zero.symm (toReal_le_of_le h.2)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
