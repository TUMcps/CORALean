module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.InterpMemCorrection
public import CORALean.Global.EuclideanNorm
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# The homogeneous solution over the first step, corrected

[1, Thm. III.2]: `R_h([0, δ]) ⊆ conv(X₀, R_h(δ)) ⊕ N` for the zonotope `X₀ = (c, g⁽¹⁾, …, g⁽ᵖ⁾)`,
`R_h(δ)` the enclosure of `Thm. III.1` and `N` built from `Lemma III.3`'s correction matrices at
`c` and at each `g⁽ⁱ⁾`. [1] derives `N = N⁽⁰⁾ ⊕ ⨁ᵢ [-1, 1]N⁽ⁱ⁾` and drops the `[-1, 1]` on the
claim that `F(g⁽ⁱ⁾)` is symmetric; its entries are not, and without the factor the theorem fails
(`printed_time_interval_counterexample`). This is the statement with `[-1, 1]` kept, from (3) at
each vector (`e_v = ‖v‖ε_norm`) and the first Arnoldi column `‖v‖Ve₁ = v`: the approximation
error at `t` is at most `t/δ` times the box of `R_h(δ)`, which the hull reaches with weight
`t/δ`. It is lines 4 and 10 of [1, Alg. 2].

## Inputs
* `A` – system matrix
* `c` – zonotope center
* `g` – zonotope generators
* `mc` – center Krylov dimension
* `Vc` – center Krylov basis
* `Hc` – center Hessenberg matrix
* `e1c` – center unit vector
* `βc` – center norm scale
* `ec` – center error rate
* `mg` – generator Krylov dimensions
* `Vg` – generator Krylov bases
* `Hg` – generator Hessenberg matrices
* `e1g` – generator unit vectors
* `βg` – generator norm scales
* `eg` – generator error rates
* `δ` – step length
* `η` – Taylor order

## Hypotheses
* `hδ` – step length positive
* `hη` – Taylor order at least one
* `hVc` – center basis maps back to the center
* `hVg` – generator bases map back to the generators
* `h3c` – center Krylov error bound
* `h3g` – generator Krylov error bounds

## Conclusion
* the time-interval solution lies in the hull plus the correction set

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the Krylov
      Subspace". IEEE Transactions on Automatic Control, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace
open scoped Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. III.2], corrected: `R_h([0, δ]) ⊆ conv(X₀, R_h(δ)) ⊕ N⁽⁰⁾ ⊕ ⨁ᵢ [-1, 1]N⁽ⁱ⁾`. -/
theorem Krylov.timeInterval_subset (A : Mat ℝ n n) (c : Vec ℝ n) (g : Fin p → Vec ℝ n)
    {mc : ℕ} (Vc : Mat ℝ n mc) (Hc : Mat ℝ mc mc) (e1c : Vec ℝ mc) (βc ec : ℝ)
    {mg : Fin p → ℕ} (Vg : ∀ i, Mat ℝ n (mg i)) (Hg : ∀ i, Mat ℝ (mg i) (mg i))
    (e1g : ∀ i, Vec ℝ (mg i)) (βg eg : Fin p → ℝ) {δ : ℝ} (hδ : 0 < δ) {η : ℕ} (hη : 1 ≤ η)
    (hVc : βc • (Vc *ᵥ e1c) = c) (hVg : ∀ i, βg i • (Vg i *ᵥ e1g i) = g i)
    (h3c : ∀ t ∈ Set.Icc 0 δ,
      ‖exp (t • A) *ᵥ c - βc • (Vc *ᵥ (exp (t • Hc) *ᵥ e1c))‖₂ ≤ ec * t)
    (h3g : ∀ i, ∀ t ∈ Set.Icc 0 δ,
      ‖exp (t • A) *ᵥ g i - βg i • (Vg i *ᵥ (exp (t • Hg i) *ᵥ e1g i))‖₂ ≤ eg i * t)
    : -- --- CONCL ---
    let X₀ : Set (Vec ℝ n) := {x | ∃ β : Fin p → ℝ, (∀ i, |β i| ≤ 1) ∧ x = c + ∑ i, β i • g i}
    let Rδ : Set (Vec ℝ n) := {y | ∃ β : Fin p → ℝ, (∀ i, |β i| ≤ 1) ∧ ∃ r : Vec ℝ n,
      (∀ j, |r j| ≤ (ec + ∑ i, eg i) * δ) ∧
      y = βc • (Vc *ᵥ (exp (δ • Hc) *ᵥ e1c))
        + ∑ i, β i • (βg i • (Vg i *ᵥ (exp (δ • Hg i) *ᵥ e1g i))) + r}
    let N : Set (Vec ℝ n) := {z | ∃ Fc ∈ Krylov.correctionSet Hc δ η, ∃ β : Fin p → ℝ,
      (∀ i, |β i| ≤ 1) ∧ ∃ F : ∀ i, Mat ℝ (mg i) (mg i),
        (∀ i, F i ∈ Krylov.correctionSet (Hg i) δ η) ∧
        z = βc • (Vc *ᵥ (Fc *ᵥ e1c)) + ∑ i, β i • (βg i • (Vg i *ᵥ (F i *ᵥ e1g i)))}
    ∀ t ∈ Set.Icc 0 δ, (exp (t • A) *ᵥ ·) '' X₀ ⊆ convexHull ℝ (X₀ ∪ Rδ) + N := by -- --- PROOF ---
  intro X₀ Rδ N t ht
  rintro _ ⟨x₀, ⟨β, hβ, rfl⟩, rfl⟩
  set lam := t / δ with hlam
  set ch : ℝ → Vec ℝ n := fun s => βc • (Vc *ᵥ (exp (s • Hc) *ᵥ e1c)) with hch
  set gh : Fin p → ℝ → Vec ℝ n := fun i s => βg i • (Vg i *ᵥ (exp (s • Hg i) *ᵥ e1g i))
    with hgh
  -- Lemma III.3 at `c` and at each `g⁽ⁱ⁾`
  obtain ⟨Fc, hFc, hc⟩ := Krylov.interp_mem_correction Vc Hc e1c βc c hVc hδ hη ht.1 ht.2
  choose F hF hg using fun i =>
    Krylov.interp_mem_correction (Vg i) (Hg i) (e1g i) (βg i) (g i) (hVg i) hδ hη ht.1 ht.2
  -- the Krylov errors at `t`, and their combination at `x₀`
  set Ec := exp (t • A) *ᵥ c - ch t with hEc
  set Eg : Fin p → Vec ℝ n := fun i => exp (t • A) *ᵥ g i - gh i t with hEg
  set E := Ec + ∑ i, β i • Eg i with hE
  have hEb : ∀ j, |E j| ≤ (ec + ∑ i, eg i) * t := by
    intro j
    have hcj := (abs_le_norm₂ Ec j).trans (h3c t ht)
    have hgj : ∀ i, |β i| * |Eg i j| ≤ eg i * t := fun i =>
      (mul_le_of_le_one_left (abs_nonneg _) (hβ i)).trans
        ((abs_le_norm₂ (Eg i) j).trans (h3g i t ht))
    rw [hE, Pi.add_apply, Finset.sum_apply, add_mul, Finset.sum_mul]
    refine (abs_add_le _ _).trans (add_le_add hcj ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)))
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact hgj i
  -- the bounds are nonnegative, read off (3) at `δ`
  have hec : 0 ≤ ec :=
    nonneg_of_mul_nonneg_left ((norm₂_nonneg _).trans (h3c δ ⟨hδ.le, le_rfl⟩)) hδ
  have heg : ∀ i, 0 ≤ eg i := fun i =>
    nonneg_of_mul_nonneg_left ((norm₂_nonneg _).trans (h3g i δ ⟨hδ.le, le_rfl⟩)) hδ
  have hS : 0 ≤ ec + ∑ i, eg i := add_nonneg hec (Finset.sum_nonneg fun i _ => heg i)
  -- the error rescaled to the box of `R_h(δ)`: `(t/δ) r = E`
  set r : Vec ℝ n := if t = 0 then 0 else (δ / t) • E with hr
  have hrE : lam • r = E := by
    by_cases ht0 : t = 0
    · have hE0 : E = 0 := funext fun j => abs_nonpos_iff.1 (by simpa [ht0] using hEb j)
      simp [hr, ht0, hE0]
    · rw [hr, if_neg ht0, smul_smul, hlam, div_mul_div_cancel₀ hδ.ne', div_self ht0, one_smul]
  have hrb : ∀ j, |r j| ≤ (ec + ∑ i, eg i) * δ := by
    intro j
    by_cases ht0 : t = 0
    · simpa [hr, ht0] using mul_nonneg hS hδ.le
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      rw [hr, if_neg ht0, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (div_pos hδ htpos)]
      calc δ / t * |E j| ≤ δ / t * ((ec + ∑ i, eg i) * t) :=
            mul_le_mul_of_nonneg_left (hEb j) (div_pos hδ htpos).le
        _ = (ec + ∑ i, eg i) * δ := by field_simp
  -- the point of the hull: weight `t/δ` on `y ∈ R_h(δ)`, the rest on `x₀`
  set y := ch δ + ∑ i, β i • gh i δ + r with hy
  have hyR : y ∈ Rδ := ⟨β, hβ, r, hrb, rfl⟩
  have hx₀ : c + ∑ i, β i • g i ∈ X₀ := ⟨β, hβ, rfl⟩
  have hlam0 : 0 ≤ lam := div_nonneg ht.1 hδ.le
  have hlam1 : lam ≤ 1 := (div_le_one hδ).2 ht.2
  have hseg : (1 - lam) • (c + ∑ i, β i • g i) + lam • y
      ∈ segment ℝ (c + ∑ i, β i • g i) y :=
    ⟨1 - lam, lam, by linarith, hlam0, by ring, rfl⟩
  have hconv : (1 - lam) • (c + ∑ i, β i • g i) + lam • y ∈ convexHull ℝ (X₀ ∪ Rδ) :=
    segment_subset_convexHull (Set.mem_union_left _ hx₀) (Set.mem_union_right _ hyR) hseg
  refine Set.mem_add.2 ⟨_, hconv,
    βc • (Vc *ᵥ (Fc *ᵥ e1c)) + ∑ i, β i • (βg i • (Vg i *ᵥ (F i *ᵥ e1g i))),
    ⟨Fc, hFc, β, hβ, F, hF, rfl⟩, ?_⟩
  -- the algebra: `e^{At}v = (1 - t/δ) v + (t/δ) v̂(δ) + n_v + E_v` at every vector
  have hexpc : exp (t • A) *ᵥ c
      = (1 - lam) • c + lam • ch δ + βc • (Vc *ᵥ (Fc *ᵥ e1c)) + Ec := by
    rw [hEc, show ch t = _ from hc]
    module
  have hexpg : ∀ i, exp (t • A) *ᵥ g i
      = (1 - lam) • g i + lam • gh i δ + βg i • (Vg i *ᵥ (F i *ᵥ e1g i)) + Eg i := by
    intro i
    show _ = _ + (exp (t • A) *ᵥ g i - gh i t)
    rw [show gh i t = _ from hg i]
    module
  show _ = exp (t • A) *ᵥ (c + ∑ i, β i • g i)
  -- both sides expanded into the same four sums over the generators
  rw [mulVec_add, mulVec_sum, hexpc, hy, smul_add lam _ r, hrE, hE]
  simp only [mulVec_smul, hexpg, smul_add, Finset.sum_add_distrib, smul_smul]
  have h1 : ∑ i, (β i * (1 - lam)) • g i = (1 - lam) • ∑ i, β i • g i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
  have h2 : ∑ i, (β i * lam) • gh i δ = lam • ∑ i, β i • gh i δ := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by module
  rw [h1, h2]
  module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
