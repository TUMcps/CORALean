module

public import CORALean.ContSet.Zonotope.Float.Theorems.TensorHBracket
public import CORALean.ContSet.Zonotope.Float.Theorems.DependentOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.TensorMultiplicationOuter

@[expose] public section

/-!
# The tensor image of a point, coefficient by coefficient, over a floating-point scalar

The exact layer's enclosure (`Real.Zonotope.tensorMultiplication_outer`) on the read-back operand of
`dependent`, which holds every point of `Z` (`dependent_outer`), gives coefficients `γ` in `[-1, 1]`
and the exact columns `H`. Each exact column differs from the stored one by at most its gap
(`tensorH_bracket`), so the stored columns with that shortfall, per coefficient, reproduce the image
of the point exactly. The hypotheses are the exact layer's: the center is the origin, and `perm`
lists every ordered triple of generator indices once, two permutations mapped to one column being
reorderings of each other.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.tensorMultiplication_coeff (Z : Zonotope (Vec 𝕋 n)) (M : Zonotope.Tensor3 𝕋 n)
    (L : Real.Zonotope.TensorLists Z.dependent.h) (hc : ∀ i, toReal (Z.c i) = 0)
    (hperm : Function.Bijective fun p : Fin L.P => (L.perm p 0, L.perm p 1, L.perm p 2))
    (hmap : ∀ p q, L.map p = L.map q →
      ({L.perm p 0, L.perm p 1, L.perm p 2} : Multiset (Fin Z.dependent.h)) =
        {L.perm q 0, L.perm q 1, L.perm q 2})
    {x : Vec ℝ n} (hx : x ∈ Z.construct) :
    ∃ γ : Fin L.C → ℝ, (∀ m, |γ m| ≤ 1)
      ∧ ∃ Δ : Fin n → Fin L.C → ℝ,
        (∀ i m, |Δ i m| ≤ toReal (Zonotope.tensorHDiff M Z.dependent L i m))
        ∧ Real.Zonotope.tensorEval (fun i a b c => toReal (M i a b c)) x
          = fun i => ∑ m,
            (toReal (Zonotope.tensorHDown M Z.dependent L i m) + Δ i m) * γ m := by -- --- PROOF ---
  -- the exact layer's enclosure, on the read-back operand of `dependent`
  have hc' : (nominal Z.dependent : Real.Zonotope (Vec ℝ n)).c = 0 := funext hc
  obtain ⟨γ, hγ, hx'⟩ := Real.Zonotope.tensorMultiplication_outer
    (nominal Z.dependent : Real.Zonotope (Vec ℝ n)) (fun i a b c => toReal (M i a b c)) L hc'
    hperm hmap (Zonotope.dependent_outer Z hx)
  -- the shortfall of each stored column
  refine ⟨γ, hγ, fun i m => (Real.Zonotope.tensorMultiplication
    (nominal Z.dependent : Real.Zonotope (Vec ℝ n)) (fun i a b c => toReal (M i a b c)) L).G m i
      - toReal (Zonotope.tensorHDown M Z.dependent L i m), fun i m => ?_, ?_⟩
  · have hb := Zonotope.tensorH_bracket M Z.dependent L i m
    have hgap := sub_le_subUp (Zonotope.tensorHUp M Z.dependent L i m)
      (Zonotope.tensorHDown M Z.dependent L i m)
    rw [abs_le]
    constructor <;> simp only [Zonotope.tensorHDiff] <;> linarith [hb.1, hb.2]
  · -- the stored columns plus their shortfalls are the exact ones
    rw [hx']
    funext i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel]
    -- the center of the exact result is the origin
    have h0 : ((nominal Z.dependent : Real.Zonotope (Vec ℝ n)).tensorMultiplication
        (fun i a b c => toReal (M i a b c)) L).c i = 0 := rfl
    rw [h0, zero_add]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
