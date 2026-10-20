module

public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeEvenContains
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

@[expose] public section

/-!
# A float polynomial zonotope lies in CORA's `zonotope(pZ)`

The exact layer's `zonotopeEven_contains` at the nominal polynomial zonotope gives a point
`c + s + Σ βⱼ G'ⱼ` with `s` the center's shift; the float generators read as the exact layer's
`G'` (a halved float is exactly half), and `s` lies between the sums of the exact shift terms
rounded down and up, so `s` plus the error box's point lies in the new error box.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* set is contained in its even-column zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float polynomial zonotope lies in its even-column zonotope. -/
theorem PolyZonotope.zonotopeEven_contains (pZ : PolyZonotope (Vec 𝕋 n)) : -- --- CONCL ---
    pZ.construct ⊆ pZ.zonotopeEven.construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  set w := Real.PolyZonotope.evenWeight pZ.E with hw
  -- the stored generators and the center's shift terms, as `zonotopeEven` writes them
  set Gw : Fin pZ.h → Vec 𝕋 n := fun l i => if ∀ k, pZ.E k l = 0 then zero
    else if ∀ k, pZ.E k l % 2 = 0 then half (pZ.G l i) else pZ.G l i with hGw
  set t : Fin pZ.h → Vec 𝕋 n := fun l i => if ∀ k, pZ.E k l = 0 then pZ.G l i
    else if ∀ k, pZ.E k l % 2 = 0 then half (pZ.G l i) else zero with ht
  -- each reads as its exact weight times the generator
  have hterm : ∀ l i, toReal (Gw l i) = w l * toReal (pZ.G l i)
      ∧ toReal (t l i) = (1 - w l) * toReal (pZ.G l i) := by
    intro l i
    simp only [hGw, ht, hw, Real.PolyZonotope.evenWeight]
    split_ifs <;> constructor <;> (try simp only [toReal_zero, toReal_half]) <;> ring
  -- the exact layer's point, center shifted by `s`
  obtain ⟨β, hβ, hzeq⟩ := Real.PolyZonotope.zonotopeEven_contains (nominal pZ) hz
  set s : Vec ℝ n := ∑ l, (1 - w l) • toRealVec (pZ.G l) with hs
  have hs_box : s ∈ (⟨fun i => sumDown fun l => t l i, fun i => sumUp fun l => t l i⟩
        : Interval (Vec 𝕋 n)).construct := by
    rw [Interval.mem_vec_iff]
    intro i
    -- `s` is the exact sum of the stored shift terms
    have hsi : s i = ∑ l, toReal (t l i) := by
      rw [hs, Finset.sum_apply]
      exact Finset.sum_congr rfl fun l _ => by
        rw [(hterm l i).2, Pi.smul_apply, smul_eq_mul]
        rfl
    rw [hsi]
    exact ⟨sumDown_le_sum _, sum_le_sumUp _⟩
  refine ⟨z - s, ⟨β, hβ, ?_⟩, s + e, Interval.plus_outer _ _ ⟨e, he, s, hs_box, add_comm e s⟩,
    by show z - s + (s + e) = z + e; rw [← add_assoc, sub_add_cancel]⟩
  -- the stored generators are the exact layer's `w • G` and `GI`
  rw [hzeq]
  show toRealVec pZ.c + s + ∑ j : Fin (pZ.h + pZ.q), β j • (nominal pZ).zonotopeEven.G j - s
    = toRealVec pZ.c + ∑ j : Fin (pZ.h + pZ.q), β j • toRealVec (pZ.zonotopeEven.G j)
  rw [add_right_comm, add_sub_cancel_right]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  -- a dependent generator, weighted; an independent one, as stored
  · funext i
    simp only [Real.PolyZonotope.zonotopeEven, PolyZonotope.zonotopeEven, Fin.append_left,
      toRealVec]
    show _ = toReal (Gw l i)
    rw [(hterm l i).1]
    show (Fin.append (fun l => w l • toRealVec (pZ.G l)) (fun j => toRealVec (pZ.GI j))
      (Fin.castAdd pZ.q l)) i = _
    rw [Fin.append_left]
    rfl
  · simp only [Real.PolyZonotope.zonotopeEven, PolyZonotope.zonotopeEven, Fin.append_right]
    show Fin.append (fun l => w l • toRealVec (pZ.G l)) (fun j => toRealVec (pZ.GI j))
      (Fin.natAdd pZ.h l) = _
    rw [Fin.append_right]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
