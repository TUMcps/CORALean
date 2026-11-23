module

public import CORALean.NN.Operations.CrownBackwardBoundFloat
public import CORALean.NN.Theorems.CrownNetBackwardLeFloat
public import CORALean.NN.Layers.Theorems.Real.CrownBoxLe

@[expose] public section

/-!
# CROWN's backward bound in floats is sound

CORA.cpp's request `backward_bound_sound`, at every `SoundFloatArithmetic`: for a float network
whose exact counterpart has its activations' inputs in their boxes `[l_k, u_k]` and its lines
holding there, the float backward bound is at most `Λ · N(x)` at every `x` of the box
`|x - x₀| ≤ r`. `CrownNet.backward_le` at `x`, the row on the box at its worst point
(`crown_box_le`), and the gap at `|x| ≤ |x₀| + r`.

## Inputs
* `F` – the float network
* `R` – the exact network
* `Λ` – the row on the outputs
* `x₀` – the box's center
* `r` – the box's radius
* `x` – a point of the box

## Hypotheses
* `hF` – `R` has `F`'s data, read as reals
* `hx` – the point lies in the box
* `hv` – every activation's input lies in its box at `x`, and the lines hold there

## Conclusion
* the float backward bound is at most the row on the outputs at `N(x)`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem CrownNet.backwardBound_le {F : CrownNet 𝕋 n k} {R : Real.CrownNet n k}
    (hF : F.Images R) (Λ : Vec 𝕋 k) (x₀ r : Vec 𝕋 n) (x : Vec ℝ n)
    (hx : ∀ j, |x j - toReal (x₀ j)| ≤ toReal (r j)) (hv : R.Holds x) : -- --- CONCL ---
    toReal (F.backwardBound Λ x₀ r) ≤ ∑ i, toReal (Λ i) * R.eval x i := by -- --- PROOF ---
  obtain ⟨hg, hback⟩ := CrownNet.backward_le hF Λ x hv
  set ρ := F.backward Λ with hρ
  -- CORA.cpp's value `v` and the allowance `w` taken from it
  set v := addDown (subDown (dotDown ρ.row x₀) (dotUp (fun j => absolute (ρ.row j)) r)) ρ.const
    with hvdef
  set w := addUp ρ.slack (dotUp ρ.gap fun j => addUp (absolute (x₀ j)) (r j)) with hw
  -- the row on the box at its worst point
  have hbox := CORALean.Real.crown_box_le (fun j => toReal (ρ.row j)) (fun j => toReal (x₀ j))
    (fun j => toReal (r j)) x hx
  -- CORA.cpp's value, rounded down
  have hv1 : toReal v ≤ ∑ j, toReal (ρ.row j) * toReal (x₀ j)
      - ∑ j, |toReal (ρ.row j)| * toReal (r j) + toReal ρ.const := by
    have h1 := le_dotUp (fun j => absolute (ρ.row j)) r
    simp only [toReal_absolute] at h1
    linarith [addDown_le_add (subDown (dotDown ρ.row x₀) (dotUp (fun j => absolute (ρ.row j)) r))
      ρ.const, subDown_le_sub (dotDown ρ.row x₀) (dotUp (fun j => absolute (ρ.row j)) r),
      dotDown_le ρ.row x₀]
  -- the input's gap at `|x| ≤ |x₀| + r`
  have hgx : ∑ j, toReal (ρ.gap j) * |x j|
      ≤ toReal (dotUp ρ.gap fun j => addUp (absolute (x₀ j)) (r j)) := by
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (le_dotUp _ _)
    refine mul_le_mul_of_nonneg_left ?_ (hg j)
    have h1 := add_le_addUp (absolute (x₀ j)) (r j)
    rw [toReal_absolute] at h1
    have h2 : |x j| ≤ |toReal (x₀ j)| + |x j - toReal (x₀ j)| := by
      have := abs_add_le (toReal (x₀ j)) (x j - toReal (x₀ j))
      simpa using this
    linarith [hx j]
  have hs := add_le_addUp ρ.slack (dotUp ρ.gap fun j => addUp (absolute (x₀ j)) (r j))
  have hfin := subDown_le_sub v w
  show toReal (subDown v w) ≤ _
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
