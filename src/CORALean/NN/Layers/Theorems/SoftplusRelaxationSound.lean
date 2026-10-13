module

public import CORALean.NN.Layers.Definitions.SoftplusBox
public import CORALean.NN.Layers.Operations.SoftplusRelaxation
public import CORALean.NN.Layers.Theorems.OfMonotoneSoundWhere
public import CORALean.NN.Layers.Theorems.Real.SoftplusMono

@[expose] public section

/-!
# The softplus relaxation is sound

For a positive stored sharpness, on the boxes where the two arguments the enclosure hands to
`logDown` and `expUp` stay in their ranges. `softplus` is monotone, so the lower end at the left
end and the upper one at the right end bound it between them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_softplus_lo_le {β : 𝕋} {k nl kl : ℕ} {l u : 𝕋} (h : SoftplusBox β k nl l u) :
    toReal ((softplusEnclosure β k nl kl).lo l) ≤
      Real.softplus (toReal β) (toReal l) := by -- --- PROOF ---
  obtain ⟨hβ, -, hD⟩ := h
  set D := onePlusExpDown k (mulDown β l) with hDdef
  -- `D` is at least one and at most `1 + exp (β l)`, so `logDown` applies and is below the log
  have h1 : 1 ≤ toReal D := by
    rw [hDdef, onePlusExpDown, toReal_maximum, toReal_one]
    exact le_max_left _ _
  have hDle : toReal D ≤ 1 + Real.exp (toReal β * toReal l) := by
    rw [hDdef, onePlusExpDown, toReal_maximum]
    have he : toReal (expDown k (mulDown β l)) ≤ Real.exp (toReal β * toReal l) :=
      le_trans (expDown_le k _) (Real.exp_le_exp.mpr (mulDown_le_mul β l))
    refine max_le ?_ (le_trans (addDown_le_add one (expDown k (mulDown β l))) ?_)
    · rw [toReal_one]
      linarith [Real.exp_pos (toReal β * toReal l)]
    · rw [toReal_one]
      linarith
  have hlog := le_trans (logDown_le nl kl D h1 hD)
    (Real.log_le_log (lt_of_lt_of_le zero_lt_one h1) hDle)
  have hdiv := divDown_le_div (logDown nl kl D) β hβ
  show toReal (divDown (logDown nl kl D) β) ≤ _
  exact le_trans hdiv (div_le_div_of_nonneg_right hlog hβ.le)

theorem aux_softplus_le_hi {β : 𝕋} {k nl kl : ℕ} {l u : 𝕋} (h : SoftplusBox β k nl l u) :
    Real.softplus (toReal β) (toReal u) ≤
      toReal ((softplusEnclosure β k nl kl).hi u) := by -- --- PROOF ---
  obtain ⟨hβ, hU, -⟩ := h
  set A := addUp one (expUp k (mulUp β u)) with hAdef
  -- `A` is at least `1 + exp (β u)`, which `expUp` covers, and `logUp` bounds its log from above
  have hexp : Real.exp (toReal β * toReal u) ≤ toReal (expUp k (mulUp β u)) :=
    le_trans (Real.exp_le_exp.mpr (mul_le_mulUp β u)) (le_expUp k _ hU)
  have hA : 1 + Real.exp (toReal β * toReal u) ≤ toReal A := by
    have := add_le_addUp one (expUp k (mulUp β u))
    rw [toReal_one] at this
    linarith
  have hpos : 0 < 1 + Real.exp (toReal β * toReal u) := by positivity
  have hlog := le_trans (Real.log_le_log hpos hA) (le_logUp nl kl A (lt_of_lt_of_le hpos hA))
  have hdiv := div_le_divUp (logUp nl kl A) β hβ
  show _ ≤ toReal (divUp (logUp nl kl A) β)
  exact le_trans (div_le_div_of_nonneg_right hlog hβ.le) hdiv


-- =======================================  MAIN THEOREM  ======================================= --

theorem softplusRelaxation_sound (β : 𝕋) (k nl kl : ℕ) :
    (softplusRelaxation β k nl kl).SoundWhere (Real.softplus (toReal β))
      (SoftplusBox β k nl) :=
  Relaxation.ofMonotone_soundWhere (E := softplusEnclosure β k nl kl)
    (fun _ _ h => Real.softplus_mono h.1) (fun _ _ h => aux_softplus_lo_le h)
    fun _ _ h => aux_softplus_le_hi h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
