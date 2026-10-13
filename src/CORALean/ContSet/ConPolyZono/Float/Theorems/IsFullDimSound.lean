import CORALean.ContSet.ConPolyZono.Float.Operations.IsFullDimWith
import CORALean.ContSet.Zonotope.Float.Theorems.BallCertReach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# A `true` from `ConPolyZono.isFullDim` proves an interior point

The factors `α = 0` satisfy the constraints, since each row `A μ(0)` lies between its bounds (its
two directed roundings do), and `μ(0)` is the zero-exponent-column indicator. So the nominal set
contains `y₀ + GI β` for every `|βⱼ| ≤ 1`, with `y₀` the centre plus the dependent generators
weighted by their monomials at `0`; the checked rows then put the open box of radius `B` around
`y₀` inside it (`Zonotope.ballCert_reach`), and the error box's lower corner keeps an interior
point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored indicator is the real monomial at the factors `0`. -/
theorem ConPolyZono.aux_zeroMonomials (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (k : Fin cPZ.s) :
    toReal (cPZ.zeroMonomials k)
      = Real.PolyZonotope.monomial cPZ.EC (fun _ => (0 : ℝ)) k := by -- --- PROOF ---
  unfold ConPolyZono.zeroMonomials Real.PolyZonotope.monomial
  by_cases h : ∀ l, cPZ.EC l k = 0
  · rw [if_pos h, toReal_one]
    exact (Finset.prod_eq_one fun l _ => by rw [h l, pow_zero]).symm
  · rw [if_neg h, toReal_zero]
    push Not at h
    obtain ⟨l, hl⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ l) (by rw [zero_pow hl])).symm

/-- A combination of the stored independent generators is their matrix applied to the weights. -/
theorem ConPolyZono.aux_sum_gi (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (β : Vec ℝ cPZ.q) :
    (∑ j, β j • (nominal cPZ).GI j)
      = toRealMat (fun i j => cPZ.GI j i) *ᵥ β := by -- --- PROOF ---
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by
    show β j * toReal (cPZ.GI j i) = toReal (cPZ.GI j i) * β j
    ring

/-- The checked rows say the factors `0` satisfy the constraints. -/
theorem ConPolyZono.aux_satisfies_zero {cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)}
    (h : ∀ i, le (cPZ.b.inf i) (dotDown (cPZ.A i) cPZ.zeroMonomials) = true
      ∧ le (dotUp (cPZ.A i) cPZ.zeroMonomials) (cPZ.b.sup i) = true) :
    cPZ.satisfies (fun _ => 0) := by -- --- PROOF ---
  intro i
  have hA : (toRealMat cPZ.A *ᵥ Real.PolyZonotope.monomial cPZ.EC (fun _ => (0 : ℝ))) i
      = ∑ k, toReal (cPZ.A i k) * toReal (cPZ.zeroMonomials k) := by
    simp only [Matrix.mulVec, dotProduct, toRealMat]
    exact Finset.sum_congr rfl fun k _ => by rw [ConPolyZono.aux_zeroMonomials]
  rw [hA]
  exact ⟨le_trans (toReal_le_of_le (h i).1) (dotDown_le (cPZ.A i) cPZ.zeroMonomials),
    le_trans (le_dotUp (cPZ.A i) cPZ.zeroMonomials) (toReal_le_of_le (h i).2)⟩

/-- The box of radius `B` around `y₀` lies in the nominal set. -/
theorem ConPolyZono.aux_box_subset {cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)} {H : Mat 𝕋 cPZ.q n} {B : 𝕋}
    (hc : Zonotope.ballCert (fun i j => cPZ.GI j i) H B one = true)
    (hsat : cPZ.satisfies (fun _ => 0)) {y₀ : Vec ℝ n}
    (hy₀ : y₀ = (nominal cPZ).c
      + ∑ i, Real.PolyZonotope.monomial (nominal cPZ).E (fun _ => 0) i • (nominal cPZ).G i)
    (y : Vec ℝ n) (hy : ∀ i, |y i - y₀ i| ≤ toReal B) : y ∈ nominalSet cPZ := by -- --- PROOF ---
  obtain ⟨-, hreach⟩ := Zonotope.ballCert_reach hc
  obtain ⟨β, hβ, hβδ⟩ := hreach (fun i => y i - y₀ i) hy
  refine ⟨fun _ => 0, β, fun k => by simp, fun j => by simpa [toReal_one] using hβδ j, hsat, ?_⟩
  show y = (nominal cPZ).c
      + ∑ i, Real.PolyZonotope.monomial (nominal cPZ).E (fun _ => 0) i • (nominal cPZ).G i
      + ∑ j, β j • (nominal cPZ).GI j
  rw [ConPolyZono.aux_sum_gi, hβ, ← hy₀]
  funext i
  show y i = y₀ i + (y i - y₀ i)
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.isFullDim_sound {cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)} {H : Mat 𝕋 cPZ.q n}
    (h : cPZ.isFullDimWith H = true) : (interior cPZ.construct).Nonempty := by -- --- PROOF ---
  simp only [ConPolyZono.isFullDimWith, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hc, hrows⟩, hE⟩ := h
  obtain ⟨hB, -⟩ := Zonotope.ballCert_reach hc
  have hsat := ConPolyZono.aux_satisfies_zero hrows
  -- the open box of radius `B` around `y₀` lies in the nominal set
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Vec ℝ n, y₀ = (nominal cPZ).c
      + ∑ i, Real.PolyZonotope.monomial (nominal cPZ).E (fun _ => 0) i • (nominal cPZ).G i :=
    ⟨_, rfl⟩
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
  have he : (fun i => toReal (cPZ.err.inf i)) ∈ (error cPZ).construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hE i)⟩
  exact ⟨_, subset_interior_add_left (Set.add_mem_add hx he)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
