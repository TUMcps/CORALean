module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.SupportBound
public import CORALean.Global.Float.FloatBound
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope

@[expose] public section

/-!
# `ConPolyZono.nominalSupportBound` over a floating-point scalar

The exact layer's `supportBound` on the stored floats: the dependent part's bound `u` over the
feasible factors, an argument as over ℝ (CORA's branch and bound under the constraints), plus
the independent block's extent `∑ⱼ |a · GIⱼ|`, each term bounded by the larger of the
upward-rounded dot product and the negated downward-rounded one and summed upward, and one more
`addUp` for the sum. An upper bound for the nominal set only; `supportBound` adds the error box.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `c` – direction as a linear functional
* `a` – float direction
* `u` – float bound on the nominal point set

## Hypotheses
* `hc` – float direction represents the functional

## Output
* float bound on the nominal set in that direction
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The nominal set's bound as a float. `cPZ.nominal.supportBound` is a real number; this is the
`𝕋` value above it, which adds the independent block's extent with every rounding upward, and
that sum is what the stored floats can compute. -/
def ConPolyZono.nominalSupportBound (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j)
    (u : FloatBound 𝕋 ((InflatedContSet.nominal cPZ).polyZonotope.point ''
      (InflatedContSet.nominal cPZ).cons.construct) c) :
    FloatBound 𝕋 (nominalSet cPZ) c :=
  let extent : Fin cPZ.qI → 𝕋 := fun j =>
    maximum (dotUp a (cPZ.GI j)) (neg (dotDown a (cPZ.GI j)))
  { val := addUp u.val (sumUp extent)
    le := fun x hx => le_trans
      (((InflatedContSet.nominal cPZ).supportBound c u.toSupportBound).le x hx)
      (by
      -- each independent generator's extent is under its rounded bound
      have h₂ : ∀ j, |c ((InflatedContSet.nominal cPZ).GI j)| ≤ toReal (extent j) := by
        intro j
        have hval : c ((InflatedContSet.nominal cPZ).GI j)
            = ∑ k, toReal (a k) * toReal (cPZ.GI j k) := hc _
        rw [hval, toReal_maximum, toReal_neg]
        refine abs_le.mpr ⟨?_, ?_⟩
        · have hdown := dotDown_le a (cPZ.GI j)
          have hm := le_max_right (toReal (dotUp a (cPZ.GI j)))
            (-toReal (dotDown a (cPZ.GI j)))
          linarith
        · have hup := le_dotUp a (cPZ.GI j)
          have hm := le_max_left (toReal (dotUp a (cPZ.GI j)))
            (-toReal (dotDown a (cPZ.GI j)))
          linarith
      -- their total, summed upward once, then added to the dependent bound
      have h₃ : (∑ j, |c ((InflatedContSet.nominal cPZ).GI j)|) ≤ toReal (sumUp extent) :=
        le_trans (Finset.sum_le_sum fun j _ => h₂ j) (sum_le_sumUp _)
      have h₄ := add_le_addUp u.val (sumUp extent)
      show toReal u.val + ∑ j, |c ((InflatedContSet.nominal cPZ).GI j)| ≤ _
      linarith) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
