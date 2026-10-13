import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapCDown
import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapCUp
import CORALean.ContSet.ConZonotope.Float.Theorems.QuadBilBracket
import CORALean.ContSet.ConZonotope.Real.Operations.QuadMap

/-!
# The exact centre of `quadMap` lies between the two stored roundings

The exact layer's centre of [1, Lemma 1] on the read-back operand, `cᵀQ c + ½ Σⱼ gⱼᵀQ gⱼ`, is
a bilinear form plus half a sum of them. Each is bracketed (`quadBil_bracket`), the sums by
`sumDown_le_sum` and `sum_le_sumUp`, and halving is exact. The stored centre is the lower end, and
the gap to the upper is what the box is charged.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.quadMapC_between (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (i : Fin m) :
    toReal (ConZonotope.quadMapCDown Q cZ i)
        ≤ (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).c i
      ∧ (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).c i
        ≤ toReal (ConZonotope.quadMapCUp Q cZ i) := by -- --- PROOF ---
  -- the exact centre, with the generators read back as `toRealVec` reads them
  have hR : (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).c i
      = toRealVec cZ.c ⬝ᵥ (toRealMat (Q i) *ᵥ toRealVec cZ.c)
        + 1 / 2 * ∑ s, (toRealVec (cZ.G s)) ⬝ᵥ
          (toRealMat (Q i) *ᵥ toRealVec (cZ.G s)) := rfl
  rw [hR]
  obtain ⟨a1, a2⟩ := ConZonotope.quadBil_bracket (Q i) cZ.c cZ.c
  -- the sum of the generators' forms, from either side
  have hs1 := sumDown_le_sum fun s =>
    ConZonotope.quadBilDown (Q i) (cZ.G s) (cZ.G s)
  have hs2 := sum_le_sumUp fun s =>
    ConZonotope.quadBilUp (Q i) (cZ.G s) (cZ.G s)
  have hlo : ∑ s, toReal (ConZonotope.quadBilDown (Q i) (cZ.G s) (cZ.G s))
      ≤ ∑ s, (toRealVec (cZ.G s)) ⬝ᵥ
          (toRealMat (Q i) *ᵥ toRealVec (cZ.G s)) :=
    Finset.sum_le_sum fun s _ => (ConZonotope.quadBil_bracket (Q i) _ _).1
  have hhi : ∑ s, (toRealVec (cZ.G s)) ⬝ᵥ
          (toRealMat (Q i) *ᵥ toRealVec (cZ.G s))
      ≤ ∑ s, toReal (ConZonotope.quadBilUp (Q i) (cZ.G s) (cZ.G s)) :=
    Finset.sum_le_sum fun s _ => (ConZonotope.quadBil_bracket (Q i) _ _).2
  have hd := addDown_le_add (ConZonotope.quadBilDown (Q i) cZ.c cZ.c)
    (half (sumDown fun s =>
      ConZonotope.quadBilDown (Q i) (cZ.G s) (cZ.G s)))
  have hu := add_le_addUp (ConZonotope.quadBilUp (Q i) cZ.c cZ.c)
    (half (sumUp fun s => ConZonotope.quadBilUp (Q i) (cZ.G s) (cZ.G s)))
  simp only [ConZonotope.quadMapCDown, ConZonotope.quadMapCUp, toReal_half] at hd hu ⊢
  constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
