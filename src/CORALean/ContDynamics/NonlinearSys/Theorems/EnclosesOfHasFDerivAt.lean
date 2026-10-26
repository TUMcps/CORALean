module

public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-!
# An interval Jacobian is a slope enclosure

`FloatModel.Encloses` asks the Jacobian boxes for slopes; this is where a model built the usual
way — an interval enclosure of the derivative over the box — supplies them. Per row `i`, the mean
value theorem on the segment from `(x', u')` to `(x, u)` gives a point `c_i` where the row's
derivative equals the difference quotient; the segment lies in the box, so the derivative there
is in the boxes. The rows come from different points, which is why the slope is asked for in a
box of matrices, entrywise. The derivative `D` is a continuous linear map on the stacked space.

## Inputs
* `fm` – float model
* `sys` – system

## Hypotheses
* `hf` – field box encloses field
* `hJ` – Jacobian boxes enclose derivative

## Conclusion
* the model encloses the system
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A box holds the segment between two of its points. -/
private theorem aux_segment_mem {k : ℕ} {I : Interval (Vec 𝕋 k)} {y y' : Vec ℝ k}
    (hy : y ∈ I.construct) (hy' : y' ∈ I.construct) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : -- --- CONCL ---
    y' + s • (y - y') ∈ I.construct := by -- --- PROOF ---
  intro i
  have h1 : toReal (I.inf i) ≤ (y i : ℝ) := (hy i).1
  have h2 : (y i : ℝ) ≤ toReal (I.sup i) := (hy i).2
  have h3 : toReal (I.inf i) ≤ (y' i : ℝ) := (hy' i).1
  have h4 : (y' i : ℝ) ≤ toReal (I.sup i) := (hy' i).2
  obtain ⟨hs0, hs1⟩ := hs
  show toReal (I.inf i) ≤ (y' i : ℝ) + s * ((y i : ℝ) - y' i)
    ∧ (y' i : ℝ) + s * ((y i : ℝ) - y' i) ≤ toReal (I.sup i)
  constructor <;> nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- A model whose `f` box holds `f` and whose Jacobian boxes hold the derivative of
`f` at every point of the box encloses `sys`. -/
theorem NonlinearSys.FloatModel.Encloses.of_hasFDerivAt
    {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m}
    (hf : ∀ (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)),
      ∀ x ∈ X.construct, ∀ u ∈ U.construct, sys.f x u ∈ (fm.f X U).construct)
    (hJ : ∀ (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)),
      ∀ x ∈ X.construct, ∀ u ∈ U.construct,
        ∃ Jx ∈ (fm.jacX X U).construct, ∃ Ju ∈ (fm.jacU X U).construct,
          ∃ D : (Vec ℝ n × Vec ℝ m) →L[ℝ] Vec ℝ n,
            HasFDerivAt (fun p : Vec ℝ n × Vec ℝ m => sys.f p.1 p.2) D (x, u) ∧
            ∀ v w, D (v, w) = Jx *ᵥ v + Ju *ᵥ w) : -- --- CONCL ---
    fm.Encloses sys := by -- --- PROOF ---
  refine ⟨hf, fun X U x hx x' hx' u hu u' hu' => ?_⟩
  set dx := x - x'
  set du := u - u'
  -- a derivative at every point of the segment, chosen once
  have hJs : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ Jx ∈ (fm.jacX X U).construct, ∃ Ju ∈ (fm.jacU X U).construct,
        ∃ D : (Vec ℝ n × Vec ℝ m) →L[ℝ] Vec ℝ n,
          HasFDerivAt (fun p : Vec ℝ n × Vec ℝ m => sys.f p.1 p.2) D (x' + s • dx, u' + s • du) ∧
          ∀ v w, D (v, w) = Jx *ᵥ v + Ju *ᵥ w := fun s hs =>
    hJ X U _ (aux_segment_mem hx hx' hs) _ (aux_segment_mem hu hu' hs)
  choose! Jx hJx Ju hJu D hD hDv using hJs
  -- the field along the segment, and its derivative there
  set g : ℝ → Vec ℝ n := fun s => sys.f (x' + s • dx) (u' + s • du)
  have hg : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (Jx s *ᵥ dx + Ju s *ᵥ du) s := by
    intro s hs
    have hp : HasDerivAt (fun s : ℝ => (x' + s • dx, u' + s • du)) (dx, du) s := by
      have h1 := ((hasDerivAt_id s).smul_const dx).const_add x'
      have h2 := ((hasDerivAt_id s).smul_const du).const_add u'
      simpa using h1.prodMk h2
    have hc := (hD s hs).comp_hasDerivAt s hp
    rw [hDv s hs] at hc
    exact hc
  -- one point of the segment per row, by the mean value theorem
  have hrow : ∀ i, ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      ((Jx c *ᵥ dx + Ju c *ᵥ du) i : ℝ) = (g 1 i : ℝ) - g 0 i := by
    intro i
    have hgi : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun s => (g s i : ℝ))
        ((Jx s *ᵥ dx + Ju s *ᵥ du) i : ℝ) s := fun s hs => hasDerivAt_pi.mp (hg s hs) i
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun s => (g s i : ℝ))
      (fun s => ((Jx s *ᵥ dx + Ju s *ᵥ du) i : ℝ)) zero_lt_one
      (fun s hs => (hgi s hs).continuousAt.continuousWithinAt)
      (fun s hs => hgi s (Set.Ioo_subset_Icc_self hs))
    refine ⟨c, hc, ?_⟩
    rw [hceq, sub_zero, div_one]
  choose c hc hceq using hrow
  have hcI : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1 := fun i => Set.Ioo_subset_Icc_self (hc i)
  -- row `i` of each slope is row `i` of the derivative at `c i`
  refine ⟨fun i j => Jx (c i) i j, fun q => ?_, fun i j => Ju (c i) i j, fun q => ?_, ?_⟩
  · exact hJx (c q.1) (hcI q.1) q
  · exact hJu (c q.1) (hcI q.1) q
  · funext i
    have h1 : g 1 = sys.f x u := by simp [g, dx, du]
    have h0 : g 0 = sys.f x' u' := by simp [g]
    have := hceq i
    rw [h1, h0] at this
    exact this.symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
