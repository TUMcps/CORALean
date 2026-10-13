module

public import CORALean.ContSet.InflatedContSet.Operations.Bound
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.SupportBound
public import CORALean.Global.Float.FloatBound

@[expose] public section

/-!
# `PolyZonotope.nominalSupportBound` over a floating-point scalar

[1, Prop. 7] on the stored floats: the dependent part's bound `u`, which is an argument as
over ℝ, plus the independent block's extent `∑ⱼ |a · GIⱼ|`, each term bounded by the
larger of the upward-rounded dot product and the negated downward-rounded one and summed
upward, and one more `addUp` for the sum.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.nominalSupportBound (pZ : PolyZonotope (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j)
    (u : FloatBound 𝕋 ((InflatedContSet.nominal pZ).subsetAt {a | ∀ k, |a k| ≤ 1}) c) :
    FloatBound 𝕋 (nominalSet pZ) c :=
  let extent : Fin pZ.q → 𝕋 := fun j =>
    maximum (dotUp a (pZ.GI j)) (neg (dotDown a (pZ.GI j)))
  { val := addUp u.val (sumUp extent)
    le := fun x hx => le_trans
      (((InflatedContSet.nominal pZ).supportBound c u.toSupportBound).le x hx)
      (by
      -- each independent generator's extent is under its rounded bound
      have h₂ : ∀ j, |c ((InflatedContSet.nominal pZ).GI j)| ≤ toReal (extent j) := by
        intro j
        have hval : c ((InflatedContSet.nominal pZ).GI j)
            = ∑ k, toReal (a k) * toReal (pZ.GI j k) := hc _
        rw [hval, toReal_maximum, toReal_neg]
        refine abs_le.mpr ⟨?_, ?_⟩
        · have hdown := dotDown_le a (pZ.GI j)
          have hm := le_max_right (toReal (dotUp a (pZ.GI j)))
            (-toReal (dotDown a (pZ.GI j)))
          linarith
        · have hup := le_dotUp a (pZ.GI j)
          have hm := le_max_left (toReal (dotUp a (pZ.GI j)))
            (-toReal (dotDown a (pZ.GI j)))
          linarith
      -- their total, summed upward once, then added to the dependent bound
      have h₃ : (∑ j, |c ((InflatedContSet.nominal pZ).GI j)|) ≤ toReal (sumUp extent) :=
        le_trans (Finset.sum_le_sum fun j _ => h₂ j) (sum_le_sumUp _)
      have h₄ := add_le_addUp u.val (sumUp extent)
      show toReal u.val + ∑ j, |c ((InflatedContSet.nominal pZ).GI j)| ≤ _
      linarith) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
