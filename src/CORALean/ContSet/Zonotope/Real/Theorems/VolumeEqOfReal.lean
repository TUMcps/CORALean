module

public import CORALean.ContSet.Zonotope.Real.Operations.Volume

@[expose] public section

/-!
# The volume of a zonotope with `n` generators

[1, Sec. IV-D, Step 2)]: for a square generator matrix the sum (7) has one term, the full index
set, so `volume(⟨c, Ĝ_b⟩) = 2ⁿ |det Ĝ_b|`. `Zonotope.volume` is (7); `volume_eq_of_h_eq` is that
it is the Lebesgue measure.

## Inputs
* `c` – center
* `Gb` – generators

## Hypotheses
* none

## Conclusion
* the volume of the square zonotope is `2ⁿ |det|`

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. IV-D]: with `n` generators, (7) is `2ⁿ |det Ĝ_b|`. -/
theorem Zonotope.volume_eq_ofReal (c : Vec ℝ n) (Gb : Fin n → Vec ℝ n) : -- --- CONCL ---
    (⟨n, c, Gb⟩ : Zonotope (Vec ℝ n)).volume
      = ENNReal.ofReal
        (2 ^ n * |(Matrix.of fun i k => Gb k i : Mat ℝ n n).det|) := by -- --- PROOF ---
  -- only the full index set has `n` elements, and its order embedding is the identity
  unfold Zonotope.volume
  congr 1
  congr 1
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin n))]
  · rw [dif_pos (Finset.card_univ.trans (Fintype.card_fin n))]
    congr 2
    have hid : ∀ k, (Finset.univ : Finset (Fin n)).orderEmbOfFin
        (Finset.card_univ.trans (Fintype.card_fin n)) k = k := fun k => by
      rw [← Finset.orderEmbOfFin_unique' (Finset.card_univ.trans (Fintype.card_fin n))
        (f := (OrderIso.refl (Fin n)).toOrderEmbedding) (fun _ => Finset.mem_univ _)]
      rfl
    simp only [hid]
  · intro S _ hS
    rw [dif_neg]
    intro hcard
    exact hS (Finset.eq_univ_of_card S (hcard.trans (Fintype.card_fin n).symm))
  · simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
