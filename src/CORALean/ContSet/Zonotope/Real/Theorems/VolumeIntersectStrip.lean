module

public import CORALean.ContSet.Zonotope.Real.Theorems.VolumeIntersectStripDet
public import CORALean.ContSet.Zonotope.Real.Theorems.DetColsSnocEqMulDotProduct

@[expose] public section

/-!
# The volume of the zonotope that bounds a zonotope-strip intersection

[1, Sec. 6.1], [2, Thm. 1]: `Vol (p̂(λ) ⊕ Ĥ(λ) Bʳ⁺¹) = Σ 2ⁿ |1 - cᵀλ| |det A_i| + Σ σ 2ⁿ |det [B_i
v_i]| |v_iᵀλ|`, with `A_i` the `n` and `B_i` the `n - 1` generators of `H` that a subset picks out
and `v_i` a unit vector normal to the columns of `B_i` (any such, one per subset; for rank `B_i < n
- 1` the term is zero whichever is taken). `Vol` is `Zonotope.volume`, the sum formula of Grover et
al. that the papers quote; `σ ≥ 0` is the strip's half-width. The proof is
`volume_intersectStrip_det` and the step `det [B_i σλ] = σ det [B_i v_i] (v_iᵀλ)`.

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 41(6):1035-1043, 2005.
* [2] J. M. Bravo, T. Alamo and E. F. Camacho. "Bounded error identification of systems with
      time-varying parameters". IEEE Transactions on Automatic Control, 51(7):1144-1150, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.volume_intersectStrip (Z : Zonotope (Vec ℝ (m+1))) (c l : Vec ℝ (m+1))
    (σ d : ℝ) (hσ : 0 ≤ σ)
    (v : (T : Finset (Fin Z.h)) → T.card = m → Vec ℝ (m+1))
    (hv : ∀ T hT, v T hT ⬝ᵥ v T hT = 1 ∧ ∀ k, v T hT ⬝ᵥ Z.G (T.orderEmbOfFin hT k) = 0) :
    (Zonotope.intersectStrip (Matrix.of fun _ j => c j : Mat ℝ 1 (m+1)) (fun _ => σ) (fun _ => d)
        (Matrix.of fun i _ => l i : Mat ℝ (m+1) 1) Z).volume =
      ENNReal.ofReal (
        (∑ S : Finset (Fin Z.h), if hS : S.card = m + 1 then
          2 ^ (m+1) * |1 - c ⬝ᵥ l| *
            |(Matrix.of fun i k => Z.G (S.orderEmbOfFin hS k) i : Mat ℝ (m+1) (m+1)).det|
          else 0) +
        (∑ T : Finset (Fin Z.h), if hT : T.card = m then
          σ * 2 ^ (m+1) * |(colsSnoc (fun k => Z.G (T.orderEmbOfFin hT k)) (v T hT)).det| *
            |v T hT ⬝ᵥ l|
          else 0)) := by -- --- PROOF ---
  rw [Zonotope.volume_intersectStrip_det]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hT : T.card = m
  · simp only [hT, dif_pos]
    rw [det_colsSnoc_eq_mul_dotProduct (v T hT) _ _ (hv T hT).1 (hv T hT).2,
      dotProduct_smul, abs_mul, smul_eq_mul, abs_mul, abs_of_nonneg hσ]
    ring
  · simp [hT]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
