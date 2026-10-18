module

public import CORALean.ContSet.Zonotope.Float.Operations.BoundaryRatioAt
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A facet row bounds the exit step

If `Zonotope.boundaryRatioAt` returns `U` at a generator selection, every step `t >= 0` with
`startPoint + t * dir` in the zonotope the stored floats describe is at most `U`. The row's vector
`C` is whatever `facetNormal` rounded to, and need not be a normal: the point is
`c + sum_j beta_j g_j` with `|beta_j| <= 1`, so `C (startPoint + t dir)` is at most
`C c + sum_j |C g_j|`, and `t` times `C dir` is at most that less `C startPoint`. Each rounding goes
the way that enlarges the bound.

Source: [1, Thm. 2].

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.boundaryRatioAt_ge (Z : Zonotope (Vec 𝕋 (n + 1))) (dir start : Vec 𝕋 (n + 1))
    (S : Fin n → Fin Z.h) (t : ℝ) (ht : 0 ≤ t)
    (hmem : toRealVec start + t • toRealVec dir ∈ nominalSet Z) : -- --- STMT ---
    ∀ U ∈ Z.boundaryRatioAt dir start S,
      t ≤ toReal U := by -- --- PROOF ---
  intro U (hU : Z.boundaryRatioAt dir start S = some U)
  unfold Zonotope.boundaryRatioAt at hU
  dsimp only at hU
  split_ifs at hU with hl
  rw [Option.some.injEq] at hU
  subst hU
  set C := Z.facetNormal S with hC
  have hden : 0 < toReal (dotDown C dir) := by
    have := toReal_lt_of_ltStrict hl
    rwa [toReal_zero] at this
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp hmem
  have hxi : ∀ i, toReal (start i) + t * toReal (dir i)
      = toReal (Z.c i) + ∑ j, toReal (Z.G j i) * β j := fun i => by
    have := hx i
    simpa [toRealVec] using this
  -- the point's product with `C`
  have hdot : ∑ k, toReal (C k) * toReal (start k) + t * ∑ k, toReal (C k) * toReal (dir k)
      = ∑ k, toReal (C k) * toReal (Z.c k)
        + ∑ j, β j * ∑ k, toReal (C k) * toReal (Z.G j k) := by
    have h1 : ∑ k, toReal (C k) * (toReal (start k) + t * toReal (dir k))
        = ∑ k, toReal (C k) * (toReal (Z.c k) + ∑ j, toReal (Z.G j k) * β j) :=
      Finset.sum_congr rfl fun k _ => by rw [hxi k]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum] at h1 ⊢
    rw [Finset.sum_comm] at h1
    have h2 : ∑ x, ∑ i, β x * (toReal (C i) * toReal (Z.G x i))
        = ∑ y, ∑ x, toReal (C x) * (toReal (Z.G y x) * β y) :=
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    have h3 : ∑ i, t * (toReal (C i) * toReal (dir i))
        = ∑ x, toReal (C x) * (t * toReal (dir x)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h2, h3]
    exact h1
  -- the magnitudes are under the rounded sum
  have hterm : ∀ j, |∑ k, toReal (C k) * toReal (Z.G j k)|
      ≤ toReal (maximum (dotUp C (Z.G j)) (neg (dotDown C (Z.G j)))) := fun j => by
    rw [toReal_maximum, toReal_neg]
    have h1 := le_dotUp C (Z.G j)
    have h2 := dotDown_le C (Z.G j)
    have h3 := le_max_left (toReal (dotUp C (Z.G j))) (-toReal (dotDown C (Z.G j)))
    have h4 := le_max_right (toReal (dotUp C (Z.G j))) (-toReal (dotDown C (Z.G j)))
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  -- the rounded sum of the generators' magnitudes along `C`
  set Δu := sumUp fun υ => maximum (dotUp C (Z.G υ)) (neg (dotDown C (Z.G υ)))
  have hsum : ∑ j, β j * ∑ k, toReal (C k) * toReal (Z.G j k) ≤ toReal Δu := by
    refine le_trans (Finset.sum_le_sum fun j _ => ?_)
      (le_trans (Finset.sum_le_sum fun j _ => hterm j) (sum_le_sumUp _))
    calc β j * ∑ k, toReal (C k) * toReal (Z.G j k)
        ≤ |β j * ∑ k, toReal (C k) * toReal (Z.G j k)| := le_abs_self _
      _ = |β j| * |∑ k, toReal (C k) * toReal (Z.G j k)| := abs_mul _ _
      _ ≤ 1 * |∑ k, toReal (C k) * toReal (Z.G j k)| :=
          mul_le_mul_of_nonneg_right (hβ j) (abs_nonneg _)
      _ = _ := one_mul _
  -- `t` times the lower end of `C dir` is under the numerator
  have hnum : t * toReal (dotDown C dir)
      ≤ toReal (subUp (addUp (dotUp C Z.c) Δu) (dotDown C start)) := by
    have hc := le_dotUp C Z.c
    have hs := dotDown_le C start
    have hd := dotDown_le C dir
    have hρ := add_le_addUp (dotUp C Z.c) Δu
    have hn := sub_le_subUp (addUp (dotUp C Z.c) Δu) (dotDown C start)
    have : t * toReal (dotDown C dir) ≤ t * ∑ k, toReal (C k) * toReal (dir k) :=
      mul_le_mul_of_nonneg_left hd ht
    linarith
  calc t ≤ _ / toReal (dotDown C dir) := (le_div_iff₀ hden).mpr hnum
    _ ≤ _ := div_le_divUp _ _ hden

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
