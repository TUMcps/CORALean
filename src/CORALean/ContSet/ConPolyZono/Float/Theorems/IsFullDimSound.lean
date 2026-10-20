module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Float.Operations.IsFullDimWith
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEqUnit
public import CORALean.ContSet.Zonotope.Float.Theorems.BallCertReach
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Pointwise
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# A `true` from `ConPolyZono.isFullDim` proves an interior point

The factors `α = 0` satisfy the constraints, each row `A μ(0)` being within its slack of `b`
(both its directed roundings are), and `μ(0)` is the zero-exponent-column indicator. So the
nominal set contains `y₀ + GI β` for every `|βⱼ| ≤ 1`, with `y₀` the center plus the dependent
generators weighted by their monomials at `0`; the checked rows then put the open box of radius
`B` around `y₀` inside it (`Zonotope.ballCert_reach`), and the error box's lower corner keeps an
interior point.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `H` – matrix of independent generators

## Hypotheses
* `h` – the test returns true

## Conclusion
* the set has an interior point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored indicator is the real monomial at the factors `0`. -/
theorem ConPolyZono.aux_zeroMonomials (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (k : Fin cPZ.cons.q) :
    toReal (cPZ.zeroMonomials k)
      = Real.PolyZonotope.monomial cPZ.cons.R (fun _ => (0 : ℝ)) k := by -- --- PROOF ---
  unfold ConPolyZono.zeroMonomials Real.PolyZonotope.monomial
  by_cases h : ∀ l, cPZ.cons.R l k = 0
  · rw [if_pos h, toReal_one]
    exact (Finset.prod_eq_one fun l _ => by rw [h l, pow_zero]).symm
  · rw [if_neg h, toReal_zero]
    push Not at h
    obtain ⟨l, hl⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ l) (by rw [zero_pow hl])).symm

/-- The checked rows say the factors `0` meet the constraints within their slack. -/
theorem ConPolyZono.aux_satisfies_zero {cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)}
    (h : ∀ i, le (subUp (cPZ.cons.b i) (dotDown (cPZ.cons.A i) cPZ.zeroMonomials))
        (absolute (cPZ.cons.b_error i)) = true
      ∧ le (subUp (dotUp (cPZ.cons.A i) cPZ.zeroMonomials) (cPZ.cons.b i))
        (absolute (cPZ.cons.b_error i)) = true) : -- --- CONCL ---
    (fun _ => 0) ∈ cPZ.cons.construct := by -- --- PROOF ---
  refine (PolyLevelSet.mem_construct_iff_of_eq_unit cPZ.cons_eq cPZ.cons_dom).mpr
    ⟨fun _ => by simp, fun i => ?_⟩
  have hA : (toRealMat cPZ.cons.A *ᵥ Real.PolyZonotope.monomial cPZ.cons.R (fun _ => (0 : ℝ))) i
      = ∑ k, toReal (cPZ.cons.A i k) * toReal (cPZ.zeroMonomials k) := by
    simp only [Matrix.mulVec, dotProduct, toRealMat]
    exact Finset.sum_congr rfl fun k _ => by rw [ConPolyZono.aux_zeroMonomials]
  rw [hA, abs_le]
  -- each end of the enclosure, its distance from `b` rounded up, within the slack
  have hlo := toReal_le_of_le (h i).1
  have hhi := toReal_le_of_le (h i).2
  rw [toReal_absolute] at hlo hhi
  have h₁ := sub_le_subUp (cPZ.cons.b i) (dotDown (cPZ.cons.A i) cPZ.zeroMonomials)
  have h₂ := sub_le_subUp (dotUp (cPZ.cons.A i) cPZ.zeroMonomials) (cPZ.cons.b i)
  have h₃ := dotDown_le (cPZ.cons.A i) cPZ.zeroMonomials
  have h₄ := le_dotUp (cPZ.cons.A i) cPZ.zeroMonomials
  constructor <;> linarith

/-- The box of radius `B` around `y₀` lies in the nominal set. -/
theorem ConPolyZono.aux_box_subset {cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)} {H : Mat 𝕋 cPZ.qI n} {B : 𝕋}
    (hc : Zonotope.ballCert (fun i j => cPZ.GI j i) H B one = true)
    (hsat : (fun _ => 0) ∈ cPZ.cons.construct) {y₀ : Vec ℝ n}
    (hy₀ : ∀ i, y₀ i = toReal (cPZ.c i)
      + ∑ l, toReal (cPZ.G l i) * Real.PolyZonotope.monomial cPZ.E (fun _ => 0) l)
    (y : Vec ℝ n) (hy : ∀ i, |y i - y₀ i| ≤ toReal B) : -- --- CONCL ---
    y ∈ nominalSet cPZ := by -- --- PROOF ---
  obtain ⟨-, hreach⟩ := Zonotope.ballCert_reach hc
  obtain ⟨β, hβ, hβδ⟩ := hreach (fun i => y i - y₀ i) hy
  refine ConPolyZono.mem_nominalSet_iff.mpr ⟨fun _ => 0, β, fun k => by simp,
    fun j => by simpa [toReal_one] using hβδ j, hsat, fun i => ?_⟩
  -- the independent block reaches exactly `y - y₀`
  have hβi : ∑ j, toReal (cPZ.GI j i) * β j = y i - y₀ i := by
    have h := congrFun hβ i
    simp only [Matrix.mulVec, dotProduct, toRealMat] at h
    exact h
  rw [hβi, ← hy₀ i]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.isFullDim_sound {cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)} {H : Mat 𝕋 cPZ.qI n}
    (h : cPZ.isFullDimWith H = true) : (interior cPZ.construct).Nonempty := by -- --- PROOF ---
  simp only [ConPolyZono.isFullDimWith, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hc, hrows⟩, hE⟩ := h
  obtain ⟨hB, -⟩ := Zonotope.ballCert_reach hc
  have hsat := ConPolyZono.aux_satisfies_zero hrows
  -- the open box of radius `B` around `y₀` lies in the nominal set
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Vec ℝ n, ∀ i, y₀ i = toReal (cPZ.c i)
      + ∑ l, toReal (cPZ.G l i) * Real.PolyZonotope.monomial cPZ.E (fun _ => 0) l :=
    ⟨_, fun _ => rfl⟩
  let V : Set (Vec ℝ n) := Set.pi Set.univ fun i =>
    Metric.ball (y₀ i) (toReal (Zonotope.ballB H one))
  have hV : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball
  have hVsub : V ⊆ nominalSet cPZ := fun y hy =>
    ConPolyZono.aux_box_subset hc hsat hy₀ y fun i => by
      have := hy i (Set.mem_univ i)
      rw [Metric.mem_ball, Real.dist_eq] at this
      exact this.le
  have hx : y₀ ∈ interior (nominalSet cPZ) :=
    interior_maximal hVsub hV fun i _ => by simpa [Metric.mem_ball] using hB
  have he : (fun i => toReal (cPZ.I_error.inf i)) ∈ (I_error cPZ).construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hE i)⟩
  exact ⟨_, subset_interior_add_left (Set.add_mem_add hx he)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
