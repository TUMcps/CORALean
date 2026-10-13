import CORALean.ContSet.HPolytope.Float.Operations.ScaleRows
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
import CORALean.ContSet.HPolytope.Float.Theorems.ScaleDevBetween

/-!
# `HPolytope.scaleRows` keeps every point of the polytope inside the domain

Each row is multiplied by a positive number and the stored row `ṽ` is `s v` rounded down. For a
point of the polytope in the domain, `ṽᵀ x = s vᵀ x - (s v - ṽ)ᵀ x`, the first term bounded by the
scaled right-hand side (rounded up) and the second from below by `scaleDevLo` (from above by
`scaleDevHi`, for the lower end of an equality's interval). So the point meets every scaled row at
the stored right-hand side. Outer over the domain: the rounding of the rows, which names other
halfspaces, is paid on the right-hand sides there, as `reduceOverDomain_outer` does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.scaleRows_outer (P : HPolytope 𝕋 (Vec 𝕋 n)) (sA : Fin P.m → 𝕋) (sE : Fin P.me → 𝕋)
    (hA : ∀ i, 0 < toReal (sA i)) (hE : ∀ i, 0 < toReal (sE i)) (dom : Interval (Vec 𝕋 n)) :
    P.construct ∩ dom.construct ⊆
      (P.scaleRows sA sE dom).construct ∩ dom.construct := by -- --- PROOF ---
  -- a point of the polytope in the domain, and its two blocks of rows
  rintro x ⟨hP, hd⟩
  refine ⟨?_, hd⟩
  obtain ⟨h1, h2⟩ := HPolytope.mem_construct_iff.mp hP
  refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
  · -- the stored row is the scaled row less the deviation
    have hsplit : (toRealMat (P.scaleRows sA sE dom).A *ᵥ x) i
        = toReal (sA i) * (toRealMat P.A *ᵥ x) i
          - ∑ j, (toReal (sA i) * toReal (P.A i j)
            - toReal (mulDown (P.A i j) (sA i))) * x j := by
      simp only [mulVec, dotProduct, toRealMat, HPolytope.scaleRows, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    -- the deviation's lower end, the right-hand side rounded up, and the scaled row
    have hdev := (HPolytope.scaleDev_between (P.A i) (sA i) dom hd).1
    have hb1 := mul_le_mulUp (P.b i) (sA i)
    have hsub := sub_le_subUp (mulUp (P.b i) (sA i)) (HPolytope.scaleDevLo (P.A i) (sA i) dom)
    have hscaled := mul_le_mul_of_nonneg_left (h1 i) (hA i).le
    show (toRealMat (P.scaleRows sA sE dom).A *ᵥ x) i ≤ toReal (subUp _ _)
    rw [hsplit]
    linarith
  · -- the same for an equality row, whose interval is widened by the deviation's range
    have hsplit : (toRealMat (P.scaleRows sA sE dom).Ae *ᵥ x) i
        = toReal (sE i) * (toRealMat P.Ae *ᵥ x) i
          - ∑ j, (toReal (sE i) * toReal (P.Ae i j)
            - toReal (mulDown (P.Ae i j) (sE i))) * x j := by
      simp only [mulVec, dotProduct, toRealMat, HPolytope.scaleRows, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    -- both ends of the deviation, and both ends of the scaled interval
    obtain ⟨hdlo, hdhi⟩ := HPolytope.scaleDev_between (P.Ae i) (sE i) dom hd
    obtain ⟨hlo, hhi⟩ := h2 i
    have hl1 := mulDown_le_mul (P.be.inf i) (sE i)
    have hu1 := mul_le_mulUp (P.be.sup i) (sE i)
    have hl2 := subDown_le_sub (mulDown (P.be.inf i) (sE i))
      (HPolytope.scaleDevHi (P.Ae i) (sE i) dom)
    have hu2 := sub_le_subUp (mulUp (P.be.sup i) (sE i))
      (HPolytope.scaleDevLo (P.Ae i) (sE i) dom)
    have hsl := mul_le_mul_of_nonneg_left hlo (hE i).le
    have hsu := mul_le_mul_of_nonneg_left hhi (hE i).le
    show toReal (subDown _ _) ≤ (toRealMat (P.scaleRows sA sE dom).Ae *ᵥ x) i ∧
      (toRealMat (P.scaleRows sA sE dom).Ae *ᵥ x) i ≤ toReal (subUp _ _)
    rw [hsplit]
    constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
