module

public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ZonotopeFold
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeEvenContains
public import CORALean.ContSet.Zonotope.Float.Theorems.PickOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

@[expose] public section

/-!
# A float polynomial zonotope lies in CORA's `zonotope(pZ)` with the shift in the center

The proof of `zonotopeEven_contains` up to its last step: a point of the set is a point of the
generators about the old center, plus the exact shift `s`, plus a point of the error box. The shift
lies between the sums of the shift terms rounded down and up; the sum rounded down is the new
center, and the box of the zero-generator zonotope of the shift reaches from it past the exact sum.
The sum of the two zonotopes lies in their `plus`.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* set is contained in its zonotope with the shift in the center
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float polynomial zonotope lies in its folded zonotope. -/
theorem PolyZonotope.zonotopeFold_contains (pZ : PolyZonotope (Vec 𝕋 n)) : -- --- CONCL ---
    pZ.toSet ⊆ pZ.zonotopeFold.toSet := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  set w := Real.PolyZonotope.evenWeight pZ.E with hw
  -- the shift terms, each its exact weight times the generator
  have hterm : ∀ l i, toReal (pZ.evenShift l i) = (1 - w l) * toReal (pZ.G l i) := by
    intro l i
    simp only [PolyZonotope.evenShift, hw, Real.PolyZonotope.evenWeight]
    split_ifs <;> (try simp only [toReal_zero, toReal_half]) <;> ring
  obtain ⟨β, hβ, hzeq⟩ := Real.PolyZonotope.zonotopeEven_contains (nominal pZ) hz
  set s : Vec ℝ n := ∑ l, (1 - w l) • toRealVec (pZ.G l) with hs
  have hsi : ∀ i, s i = ∑ l, toReal (pZ.evenShift l i) := by
    intro i
    rw [hs, Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => by
      rw [hterm l i, Pi.smul_apply, smul_eq_mul]
      rfl
  -- the generators of `zonotopeEven` are the exact layer's, weighted
  have hG : ∀ j, toRealVec (pZ.zonotopeEven.G j) = (nominal pZ).zonotopeEven.G j := by
    intro j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · funext i
      have hl : toReal (pZ.zonotopeEven.G (Fin.castAdd pZ.q l) i) = w l * toReal (pZ.G l i) := by
        simp only [PolyZonotope.zonotopeEven, Fin.append_left, hw, Real.PolyZonotope.evenWeight]
        split_ifs <;> (try simp only [toReal_zero, toReal_half]) <;> ring
      simp only [Real.PolyZonotope.zonotopeEven, toRealVec]
      show toReal (pZ.zonotopeEven.G (Fin.castAdd pZ.q l) i) = _
      rw [hl]
      show _ = (Fin.append (fun l => w l • toRealVec (pZ.G l)) (fun j => toRealVec (pZ.GI j))
        (Fin.castAdd pZ.q l)) i
      rw [Fin.append_left]
      rfl
    · simp only [Real.PolyZonotope.zonotopeEven, PolyZonotope.zonotopeEven, Fin.append_right]
      show _ = Fin.append (fun l => w l • toRealVec (pZ.G l)) (fun j => toRealVec (pZ.GI j))
        (Fin.natAdd pZ.h l)
      rw [Fin.append_right]
  -- the old center and the generators reach `z - s`
  have hzs : z - s = toRealVec pZ.c
      + ∑ j : Fin (pZ.h + pZ.q), β j • toRealVec (pZ.zonotopeEven.G j) := by
    rw [hzeq]
    simp only [hG]
    show toRealVec pZ.c + s + ∑ j : Fin (pZ.h + pZ.q), β j • (nominal pZ).zonotopeEven.G j - s
      = toRealVec pZ.c + ∑ j : Fin (pZ.h + pZ.q), β j • (nominal pZ).zonotopeEven.G j
    rw [add_right_comm, add_sub_cancel_right]
  -- the point about the old center plus the error lies in the zonotope of the old generators
  have hZ : z - s + e ∈ (⟨pZ.zonotopeEven.h, pZ.c, pZ.zonotopeEven.G, pZ.I_error⟩ :
      Zonotope (Vec 𝕋 n)).toSet := by
    refine ⟨z - s, ?_, e, he, rfl⟩
    refine Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun i => ?_⟩
    have h1 := congrFun hzs i
    rw [h1]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toRealVec]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)
  -- the shift is a point of the zonotope that holds it
  have hs_mem : s ∈ (⟨0, fun i => sumDown fun l => pZ.evenShift l i, Fin.elim0,
      ⟨fun _ => zero, fun i => subUp (sumUp fun l => pZ.evenShift l i)
        (sumDown fun l => pZ.evenShift l i)⟩⟩ : Zonotope (Vec 𝕋 n)).toSet := by
    refine ⟨fun i => toReal (sumDown fun l => pZ.evenShift l i), ?_,
      s - fun i => toReal (sumDown fun l => pZ.evenShift l i), ?_, by simp⟩
    -- the center part is the point itself; the rest lies in the error box
    · exact Zonotope.mem_nominalSet_iff.mpr ⟨fun j => j.elim0, fun j => j.elim0, fun i => by simp⟩
    · rw [Interval.mem_vec_iff]
      intro i
      have hle := sumDown_le_sum fun l => pZ.evenShift l i
      have hge := sum_le_sumUp fun l => pZ.evenShift l i
      have hsub := add_le_addUp (sumUp fun l => pZ.evenShift l i)
        (neg (sumDown fun l => pZ.evenShift l i))
      rw [toReal_neg] at hsub
      refine ⟨?_, ?_⟩
      · show toReal (zero : 𝕋) ≤ _
        rw [toReal_zero]
        simp only [Pi.sub_apply, hsi]
        linarith
      · show _ ≤ toReal (addUp _ (neg _))
        simp only [Pi.sub_apply, hsi]
        linarith
  -- adding the shift gives the point
  have hfin : z - s + e + s ∈ pZ.zonotopeFold.toSet :=
    Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.pick_outer _ _ _ hZ) hs_mem)
  have heq : z - s + e + s = z + e := by abel
  rw [heq] at hfin
  exact hfin

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
