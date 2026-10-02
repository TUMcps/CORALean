import CORALean.Global.BoxDiameter
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Tactic.Positivity

/-!
# The box diameter of a Minkowski sum, against the diameters of its summands

`d(box(X ⊕ Y))` read coordinatewise is a difference of two points of `X + Y`,
each splitting into an `X`-part and a `Y`-part, so it is bounded by the sum of
the two summands' own diameters — the triangle inequality [1, Lemma 2]'s
Appendix B proof takes for granted between a scaled error set and a step's
own abstraction error.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A Minkowski sum's box diameter is at most the sum of its summands' own. -/
theorem boxDiameter_add_le {X Y : Set (Vec ℝ n)} (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y) :
    ‖boxDiameter (X + Y)‖ ≤ ‖boxDiameter X‖ + ‖boxDiameter Y‖ := by -- --- PROOF ---
  have hne : (X + Y).Nonempty := hXne.add hYne
  -- read `X + Y`'s coordinate `i` as a sum-of-projections image over `X ×ˢ Y`
  have hcoord : ∀ i : Fin n, boxDiameter (X + Y) i ≤ ‖boxDiameter X‖ + ‖boxDiameter Y‖ := by
    intro i
    have himg : (fun z : Vec ℝ n => z i) '' (X + Y)
        = (fun p : Vec ℝ n × Vec ℝ n => p.1 i + p.2 i) '' (X ×ˢ Y) := by
      ext v; constructor
      · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    -- each summand's own gap is under its own diameter, and the two gaps add
    have hkey : ∀ a ∈ X, ∀ b ∈ Y, ∀ a' ∈ X, ∀ b' ∈ Y,
        (a i + b i) - (a' i + b' i) ≤ ‖boxDiameter X‖ + ‖boxDiameter Y‖ := by
      intro a ha b hb a' ha' b' hb'
      have h1 : a i - a' i ≤ ‖boxDiameter X‖ :=
        (le_abs_self _).trans ((abs_sub_le_boxDiameter hX ha ha' i).trans
          ((le_abs_self _).trans (norm_le_pi_norm (boxDiameter X) i)))
      have h2 : b i - b' i ≤ ‖boxDiameter Y‖ :=
        (le_abs_self _).trans ((abs_sub_le_boxDiameter hY hb hb' i).trans
          ((le_abs_self _).trans (norm_le_pi_norm (boxDiameter Y) i)))
      linarith
    -- sandwich `sSup` between `sInf` and the bound, exactly as `hkey` allows
    have hprodne : (X ×ˢ Y).Nonempty := hXne.prod hYne
    have hsup : sSup ((fun z : Vec ℝ n => z i) '' (X + Y))
        ≤ sInf ((fun z : Vec ℝ n => z i) '' (X + Y)) + (‖boxDiameter X‖ + ‖boxDiameter Y‖) := by
      rw [himg]
      refine csSup_le (hprodne.image _) ?_
      rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      have h : (a i + b i) - (‖boxDiameter X‖ + ‖boxDiameter Y‖)
          ≤ sInf ((fun p : Vec ℝ n × Vec ℝ n => p.1 i + p.2 i) '' (X ×ˢ Y)) := by
        refine le_csInf (hprodne.image _) ?_
        rintro _ ⟨⟨a', b'⟩, ⟨ha', hb'⟩, rfl⟩
        linarith [hkey a ha b hb a' ha' b' hb']
      linarith
    rw [boxDiameter]; linarith
  -- `X + Y` is bounded, so its box diameter is nonnegative and its norm reads off coordinates
  have hb : Bornology.IsBounded (X + Y) := hX.add hY
  have hnn : ∀ i : Fin n, 0 ≤ boxDiameter (X + Y) i := fun i => by
    have h1 : sInf ((fun z : Vec ℝ n => z i) '' (X + Y))
        ≤ sSup ((fun z : Vec ℝ n => z i) '' (X + Y)) :=
      csInf_le_csSup (hne.image _) (bddBelow_eval_image hb i) (bddAbove_eval_image hb i)
    rw [boxDiameter]; linarith
  rw [pi_norm_le_iff_of_nonneg
    (by positivity : (0:ℝ) ≤ ‖boxDiameter X‖ + ‖boxDiameter Y‖)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn i)]
  exact hcoord i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
