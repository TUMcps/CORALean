module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Diagonal

@[expose] public section

/-!
# The volume of the reduction's parallelotope

[1, Sec. 4.3 (new reduction)]: the parallelotope that replaces `X = {[T v], c}` is
`X̃ = {[T(I + diag|r|)], c}`, and "using the standard formula for the volume of a zonotope ...
and standard properties of the determinant, `v(X̃) = 2ⁿ|det T det(I + diag|r|)| =
2ⁿ|det T| Πᵢ(1 + |rᵢ|)`". A parallelotope is the image of the box `[-1, 1]ⁿ`, of volume `2ⁿ`,
under its generator matrix, translated by the center: the volume is `2ⁿ` times the absolute
determinant, and `det(I + diag|r|) = Πᵢ(1 + |rᵢ|)`.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.3 (new reduction)]: `v(X̃) = 2ⁿ|det T| Πᵢ(1 + |rᵢ|)`. -/
theorem Zonotope.reduceScott_parallelotope_volume {n : ℕ} (c : Vec ℝ n) (T : Mat ℝ n n)
    (r : Vec ℝ n) : -- --- STMT ---
    volume (⟨n, c, fun i a => (T * diagonal fun k => 1 + |r k|) a i⟩
        : Zonotope (Vec ℝ n)).construct
      = ENNReal.ofReal (2 ^ n * |T.det| * ∏ i, (1 + |r i|)) := by -- --- PROOF ---
  set M : Mat ℝ n n := T * diagonal fun k => 1 + |r k| with hM
  set box : Set (Vec ℝ n) := Set.Icc (fun _ => -1) (fun _ => 1) with hbox
  -- the parallelotope is the box under `M`, translated by `c`
  have hset : (⟨n, c, fun i a => M a i⟩ : Zonotope (Vec ℝ n)).construct
      = (fun z => -c + z) ⁻¹' (Matrix.toLin' M '' box) := by
    ext z
    have hsum : ∀ β : Fin n → ℝ, ∑ j, β j • (fun a => M a j) = M *ᵥ β := fun β => by
      funext a
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    simp only [Zonotope.construct, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image,
      Matrix.toLin'_apply, hbox, Set.mem_Icc]
    constructor
    · rintro ⟨β, hβ, rfl⟩
      refine ⟨β, ⟨fun k => (abs_le.mp (hβ k)).1, fun k => (abs_le.mp (hβ k)).2⟩, ?_⟩
      rw [hsum]; abel
    · rintro ⟨β, ⟨h1, h2⟩, hz⟩
      refine ⟨β, fun k => abs_le.mpr ⟨h1 k, h2 k⟩, ?_⟩
      rw [hsum, hz]; abel
  -- translation keeps volume; `M` scales it by `|det M|`; the box has volume `2ⁿ`
  rw [hset, measure_preimage_add, Measure.addHaar_image_linearMap, LinearMap.det_toLin', hbox,
    Real.volume_Icc_pi]
  have hdet : M.det = T.det * ∏ i, (1 + |r i|) := by rw [hM, det_mul, det_diagonal]
  have hprod : ∏ _i : Fin n, ENNReal.ofReal (1 - -1) = ENNReal.ofReal (2 ^ n) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have hp : 0 ≤ ∏ i, (1 + |r i|) := Finset.prod_nonneg fun i _ => by positivity
  rw [hprod, ← ENNReal.ofReal_mul (abs_nonneg _), hdet, abs_mul, abs_of_nonneg hp]
  congr 1
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
