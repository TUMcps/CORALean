module

public import CORALean.NN.Layers.Operations.RootLineRelaxation
public import CORALean.NN.Layers.Theorems.OfBandEnclosesWhere
public import CORALean.Global.Float.SqrtDownCoraLe
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

@[expose] public section

/-!
# The line of the square root is sound

At the stored slope `m`, whatever it came to, `g(x) = √x - m x` is concave on `x ≥ 0`, so on
`[l, u]` it is at least the smaller of `g(l)` and `g(u)`, each rounded down. For `m > 0`,
`1 / (4 m) - g(x) = (2 m √x - 1)² / (4 m) ≥ 0`; for `m ≤ 0`, `g` grows and `g(u)` is the largest;
otherwise `√x ≤ √u` and `-m x` is at most its larger end value. The margin is zero, so
`Relaxation.ofBand_enclosesWhere` concludes, on the boxes with `0 ≤ l`.

## Inputs
* `regression` – the least-squares slope, else Singh's
* `p` – the square root's Newton steps

## Hypotheses
* none

## Conclusion
* the line is sound for the square root on the boxes with `0 ≤ l`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `√t - m t` on `[l, u] ⊆ [0, ∞)` is at least the smaller of its end values. -/
private theorem aux_min_le (m : ℝ) {l u t : ℝ} (h0 : 0 ≤ l) (hl : l ≤ t)
    (hu : t ≤ u) : -- --- CONCL ---
    min (Real.sqrt l - m * l) (Real.sqrt u - m * u) ≤ Real.sqrt t - m * t := by -- --- PROOF ---
  have hconc : ConcaveOn ℝ (Set.Ici 0) (fun x => Real.sqrt x - m * x) :=
    (Real.strictConcaveOn_sqrt.concaveOn.sub ((LinearMap.mul ℝ ℝ m).convexOn (convex_Ici 0))).congr
      (fun x _ => by simp)
  exact hconc.min_le_of_mem_Icc (Set.mem_Ici.2 h0) (Set.mem_Ici.2 (h0.trans (hl.trans hu)))
    ⟨hl, hu⟩

/-- For `m > 0`, `√t - m t` is at most `1 / (4 m)`, its maximum over the half-line. -/
private theorem aux_le_closed {m : ℝ} (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) : -- --- CONCL ---
    Real.sqrt t - m * t ≤ 1 / m / 2 / 2 := by -- --- PROOF ---
  have hs := Real.sq_sqrt ht
  have key : 4 * m * (Real.sqrt t - m * t) ≤ 1 := by
    have e : 4 * m * (Real.sqrt t - m * Real.sqrt t ^ 2) = 1 - (2 * m * Real.sqrt t - 1) ^ 2 := by
      ring
    rw [hs] at e
    nlinarith [sq_nonneg (2 * m * Real.sqrt t - 1)]
  have h4 : 1 / m / 2 / 2 = 1 / (4 * m) := by ring
  rw [h4, le_div_iff₀ (by positivity)]
  linarith

/-- `x` from below or above is `x` in the real line's order, the bounds of `√x - m x`. -/
private theorem aux_g_bounds (p : ℕ) (m x : 𝕋) : -- --- CONCL ---
    toReal (subDown (sqrtDownCora p x) (mulUp m x)) ≤
        Real.sqrt (toReal x) - toReal m * toReal x ∧
      Real.sqrt (toReal x) - toReal m * toReal x ≤
        toReal (subUp (sqrtUp p x) (mulDown m x)) := by -- --- PROOF ---
  have h1 := subDown_le_sub (sqrtDownCora p x) (mulUp m x)
  have h2 := mul_le_mulUp m x
  have h3 := sqrtDownCora_le p x
  have h4 := sub_le_subUp (sqrtUp p x) (mulDown m x)
  have h5 := mulDown_le_mul m x
  have h6 := le_sqrtUp p x
  constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem rootLineRelaxation_enclosesWhere (regression : Bool) (p : ℕ) : -- --- CONCL ---
    (rootLineRelaxation (𝕋 := 𝕋) regression p).EnclosesWhere Real.sqrt
      fun l _ => 0 ≤ toReal l := by -- --- PROOF ---
  refine Relaxation.ofBand_enclosesWhere (fun {l u t} hP hl hu => ?_)
    (fun _ => by rw [toReal_zero])
  set m := step_rootLineSlope regression p l u with hmdef
  have ht0 : 0 ≤ t := le_trans hP hl
  obtain ⟨hgl, hgl'⟩ := aux_g_bounds p m l
  obtain ⟨hgu, hgu'⟩ := aux_g_bounds p m u
  have hmin := aux_min_le (toReal m) hP hl hu
  constructor
  · -- the lower end: the smaller end value, by concavity
    show toReal (step_rootLineLo regression p l u) ≤ _
    unfold step_rootLineLo
    rw [← hmdef]
    dsimp only [step_rootLineEnclosure]
    rw [toReal_minimum]
    exact le_trans (min_le_min hgl hgu) hmin
  · -- the upper end: the closed-form maximum, the larger end value, or `√u - m x`
    show _ ≤ toReal (step_rootLineHi regression p l u)
    unfold step_rootLineHi
    rw [← hmdef]
    dsimp only [step_rootLineEnclosure]
    have hends : Real.sqrt (toReal u) - toReal m * toReal u ≤
        toReal (maximum (subUp (sqrtUp p l) (mulDown m l)) (subUp (sqrtUp p u) (mulDown m u))) := by
      rw [toReal_maximum]; exact le_trans hgu' (le_max_right _ _)
    split_ifs with h1 h2
    · -- `m > 0`: `1 / (4 m)`, the quotient rounded up
      have hm := toReal_lt_of_ltStrict h1
      rw [toReal_zero] at hm
      have hq := div_le_divUp one m hm
      rw [toReal_one] at hq
      rw [toReal_maximum, toReal_half, toReal_half]
      refine le_trans (aux_le_closed hm t ht0) (le_trans ?_ (le_max_right _ _))
      linarith
    · -- `m ≤ 0`: `g` grows, `g(u)` is the largest
      have hm := toReal_le_of_le h2
      rw [toReal_zero] at hm
      have hs := Real.sqrt_le_sqrt hu
      nlinarith
    · -- neither: `√x ≤ √u`, and `-m x` at most its larger end value
      have hs := Real.sqrt_le_sqrt hu
      have hsu := le_sqrtUp p u
      have ha := add_le_addUp (sqrtUp p u) (maximum (neg (mulDown m l)) (neg (mulDown m u)))
      have hl' := mulDown_le_mul m l
      have hu' := mulDown_le_mul m u
      rw [toReal_maximum, toReal_neg, toReal_neg] at ha
      have hlin : -(toReal m * t) ≤ max (-toReal (mulDown m l)) (-toReal (mulDown m u)) := by
        rcases le_total 0 (toReal m) with h | h
        · exact le_trans (by nlinarith) (le_max_left _ _)
        · exact le_trans (by nlinarith) (le_max_right _ _)
      linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
