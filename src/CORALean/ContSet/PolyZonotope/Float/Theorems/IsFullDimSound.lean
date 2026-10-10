import CORALean.ContSet.PolyZonotope.Float.Operations.IsFullDimWith
import CORALean.ContSet.Zonotope.Float.Theorems.BallCertReach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# A `true` from `PolyZonotope.isFullDim` proves an interior point

At the factors `α = 0` the nominal set contains `y₀ + GI β` for every `|βⱼ| ≤ 1`, where `y₀` is
the centre plus the dependent generators weighted by their monomials at `0`. The checked rows put
every vector within `B` of zero in that zonotope's span with such coefficients
(`Zonotope.ballCert_reach`), so the open box of radius `B` around `y₀` lies inside the set.
Adding the error box's lower corner keeps an interior point (`subset_interior_add_left`).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A combination of the stored independent generators is their matrix applied to the weights. -/
theorem PolyZonotope.aux_sum_gi (pZ : PolyZonotope 𝕋 n) (β : Vec ℝ pZ.q) :
    (∑ j, β j • (nominal pZ).GI j)
      = toRealMat (fun i j => pZ.GI j i) *ᵥ β := by -- --- PROOF ---
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by
    show β j * toReal (pZ.GI j i) = toReal (pZ.GI j i) * β j
    ring

/-- The box of radius `B` around `y₀` lies in the nominal set. -/
theorem PolyZonotope.aux_box_subset {pZ : PolyZonotope 𝕋 n} {H : Mat 𝕋 pZ.q n} {B : 𝕋}
    (hc : Zonotope.ballCert (fun i j => pZ.GI j i) H B one = true) {y₀ : Vec ℝ n}
    (hy₀ : y₀ = (nominal pZ).c
      + ∑ i, Real.PolyZonotope.monomial (nominal pZ).E (fun _ => 0) i • (nominal pZ).G i)
    (y : Vec ℝ n) (hy : ∀ i, |y i - y₀ i| ≤ toReal B) : y ∈ nominalSet pZ := by -- --- PROOF ---
  obtain ⟨-, hreach⟩ := Zonotope.ballCert_reach hc
  obtain ⟨β, hβ, hβδ⟩ := hreach (fun i => y i - y₀ i) hy
  refine ⟨fun _ => 0, β, fun k => by simp, fun j => by simpa [toReal_one] using hβδ j, ?_⟩
  show y = (nominal pZ).c
      + ∑ i, Real.PolyZonotope.monomial (nominal pZ).E (fun _ => 0) i • (nominal pZ).G i
      + ∑ j, β j • (nominal pZ).GI j
  rw [PolyZonotope.aux_sum_gi, hβ, ← hy₀]
  funext i
  show y i = y₀ i + (y i - y₀ i)
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.isFullDim_sound {pZ : PolyZonotope 𝕋 n} {H : Mat 𝕋 pZ.q n}
    (h : pZ.isFullDimWith H = true) : (interior pZ.construct).Nonempty := by -- --- PROOF ---
  simp only [PolyZonotope.isFullDimWith, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨hc, hE⟩ := h
  obtain ⟨hB, -⟩ := Zonotope.ballCert_reach hc
  -- the open box of radius `B` around `y₀` lies in the nominal set
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Vec ℝ n, y₀ = (nominal pZ).c
      + ∑ i, Real.PolyZonotope.monomial (nominal pZ).E (fun _ => 0) i • (nominal pZ).G i :=
    ⟨_, rfl⟩
  let V : Set (Vec ℝ n) := Set.pi Set.univ fun i =>
    Metric.ball (y₀ i) (toReal (Zonotope.ballB H one))
  have hV : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball
  have hVsub : V ⊆ nominalSet pZ := fun y hy =>
    PolyZonotope.aux_box_subset hc hy₀ y fun i => by
      have := hy i (Set.mem_univ i)
      rw [Metric.mem_ball, Real.dist_eq] at this
      exact this.le
  have hx : y₀ ∈ interior (nominalSet pZ) :=
    interior_maximal hVsub hV fun i _ => by simpa [Metric.mem_ball] using hB
  have he : (fun i => toReal (pZ.err.inf i)) ∈ (error pZ).construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hE i)⟩
  exact ⟨_, subset_interior_add_left (Set.add_mem_add hx he)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
