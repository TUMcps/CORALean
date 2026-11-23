module

public import CORALean.NN.Layers.Operations.RelaxationOfBand

@[expose] public section

/-!
# A relaxation from a band is sound

If `σ(t) - s t` lies in `[lo, hi]` for every `t` of a box `P` holds on, and the margin is not
negative, the middle `c` is below `(hi + lo) / 2` by at most half the spread of `hi + lo` between
its two roundings: `σ(t) - s t - c` is at most half the width plus that, and `c - (σ(t) - s t)` at
most half the width.

## Inputs
* `s` – the slope on a box
* `lo` – the band's lower end on a box
* `hi` – the band's upper end on a box
* `b` – the margin on a box
* `σ` – the function
* `P` – the boxes the band holds on

## Hypotheses
* `hband` – on those boxes, `σ(t) - s t` lies between the two ends
* `hb` – the margin is not negative there

## Conclusion
* the relaxation is sound for `σ` on those boxes
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Relaxation.ofBand_enclosesWhere {s lo hi b : 𝕋 → 𝕋 → 𝕋} {σ : ℝ → ℝ}
    {P : 𝕋 → 𝕋 → Prop}
    (hband : ∀ {l u : 𝕋} {t : ℝ}, P l u → toReal l ≤ t → t ≤ toReal u →
      toReal (lo l u) ≤ σ t - toReal (s l u) * t ∧ σ t - toReal (s l u) * t ≤ toReal (hi l u))
    (hb : ∀ {l u : 𝕋}, P l u → 0 ≤ toReal (b l u)) : -- --- CONCL ---
    (Relaxation.ofBand s lo hi b).EnclosesWhere σ P := by -- --- PROOF ---
  refine ⟨fun {l u t} hP hl hu => ?_⟩
  obtain ⟨hlo, hhi⟩ := hband hP hl hu
  have hb0 := hb hP
  -- the middle, its two roundings, the width and the spread
  have hsD := addDown_le_add (hi l u) (lo l u)
  have hsU := add_le_addUp (hi l u) (lo l u)
  have hw := sub_le_subUp (hi l u) (lo l u)
  have hsp := sub_le_subUp (addUp (hi l u) (lo l u)) (addDown (hi l u) (lo l u))
  have he1 := add_le_addUp (half (subUp (hi l u) (lo l u)))
    (half (subUp (addUp (hi l u) (lo l u)) (addDown (hi l u) (lo l u))))
  have he2 := add_le_addUp (addUp (half (subUp (hi l u) (lo l u)))
    (half (subUp (addUp (hi l u) (lo l u)) (addDown (hi l u) (lo l u))))) (b l u)
  simp only [toReal_half] at he1 he2
  show |σ t - (toReal (s l u) * t + toReal (half (addDown (hi l u) (lo l u))))|
    ≤ toReal (addUp (addUp (half (subUp (hi l u) (lo l u)))
      (half (subUp (addUp (hi l u) (lo l u)) (addDown (hi l u) (lo l u))))) (b l u))
  rw [toReal_half, abs_le]
  constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
