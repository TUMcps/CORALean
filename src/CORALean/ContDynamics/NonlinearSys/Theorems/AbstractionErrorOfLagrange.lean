import CORALean.ContDynamics.NonlinearSys.Definitions.AbstractionError
import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
import CORALean.ContSet.Interval.Real.Instances
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# A twice-differentiable field, taken one order further

[1, Sec. 4.1], and `AbstractionErrorOfHessian` carried one order up: where
`A, B` are the derivative of `f` at `(xs, us)` and `Q` is (half) the exact
Hessian there, `lagrangeRemainder` certifies what is left of `f` once the
affine part *and* the exact quadratic part are both subtracted, provided `E`
bounds the third derivative entrywise on a neighbourhood.

The result is stated as an `AbstractionError` of the *shifted* field, its exact
quadratic term subtracted out: `AbstractionError` has no slot for one, and
shifting it there reuses that type rather than inventing one. A caller wanting
a certificate for `f` itself still has to enclose the quadratic term
separately — CORA's `sq(D, ·)`; this repository's dependency-preserving
analogue is `precompStatError`, whose own `Q` is state-only, while this file's
is exact over the full stacked `(x, u)`, so the two do not yet compose.

`Ef` is `Hf`'s own derivative, the step `Hf` is from `Ff`; `hEb` bounds it as
`hHb` bounds `Hf` in the order-one file.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Set ContSet

variable {d n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A function below a boundary at `0` whose slope stays below the boundary's
stays below it on all of `[0, 1]`. -/
theorem aux_le_of_deriv_le {g g' B B' : ℝ → ℝ}
    (hg : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt g (g' t) t) (hB : ∀ t, HasDerivAt B (B' t) t)
    (h0 : g 0 ≤ B 0) (hle : ∀ t ∈ Icc (0:ℝ) 1, g' t ≤ B' t) :
    ∀ t ∈ Icc (0:ℝ) 1, g t ≤ B t :=
  fun _ ht => image_le_of_deriv_right_le_deriv_boundary
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt) h0
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
    (fun t ht => hle t (Ico_subset_Icc_self ht)) ht

/-- Taylor at order two with the remainder bounded rather than evaluated: no
third derivative is named at an unknown point, only bounded. -/
theorem aux_abs_taylor_le2 {φ φ' φ'' φ''' : ℝ → ℝ} {K : ℝ}
    (hφ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt φ' (φ'' t) t)
    (hφ'' : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt φ'' (φ''' t) t)
    (hK : ∀ t ∈ Icc (0:ℝ) 1, |φ''' t| ≤ K) :
    |φ 1 - φ 0 - φ' 0 - φ'' 0 / 2| ≤ K / 6 := by -- --- PROOF ---
  have hlin : ∀ s : ℝ, HasDerivAt (fun t : ℝ => K * t) K s := fun s => by
    simpa using (hasDerivAt_id s).const_mul K
  have hid2 : ∀ s : ℝ, HasDerivAt (fun t : ℝ => t * φ'' 0) (φ'' 0) s := fun s => by
    simpa using (hasDerivAt_id s).mul_const (φ'' 0)
  have hquad : ∀ s : ℝ, HasDerivAt (fun t : ℝ => K * t ^ 2 / 2) (K * s) s := fun s => by
    have h := ((hasDerivAt_pow 2 s).const_mul K).div_const 2
    norm_num at h
    rwa [show K * (2 * s) / 2 = K * s by ring] at h
  have hid1 : ∀ s : ℝ, HasDerivAt (fun t : ℝ => t * φ' 0) (φ' 0) s := fun s => by
    simpa using (hasDerivAt_id s).mul_const (φ' 0)
  have hquadhalf : ∀ s : ℝ, HasDerivAt (fun t : ℝ => t ^ 2 / 2 * φ'' 0) (s * φ'' 0) s := fun s => by
    have h := ((hasDerivAt_pow 2 s).div_const 2).mul_const (φ'' 0)
    norm_num at h
    exact h
  have hcube : ∀ s : ℝ, HasDerivAt (fun t : ℝ => K * t ^ 3 / 6) (K * s ^ 2 / 2) s := fun s => by
    have h := ((hasDerivAt_pow 3 s).const_mul K).div_const 6
    norm_num at h
    rwa [show K * (3 * s ^ 2) / 6 = K * s ^ 2 / 2 by ring] at h
  -- the second derivative leaves `φ''(0)` no faster than `K`, in either direction
  have hup2 : ∀ t ∈ Icc (0:ℝ) 1, φ'' t - φ'' 0 ≤ K * t :=
    aux_le_of_deriv_le (fun t ht => (hφ'' t ht).sub_const _) hlin (by simp)
      (fun t ht => (abs_le.1 (hK t ht)).2)
  have hdn2 : ∀ t ∈ Icc (0:ℝ) 1, φ'' 0 - φ'' t ≤ K * t := by
    refine aux_le_of_deriv_le (g := fun t => φ'' 0 - φ'' t) (g' := fun t => -φ''' t)
      (fun t ht => (hφ'' t ht).const_sub (φ'' 0)) hlin (by simp) (fun t ht => ?_)
    have := (abs_le.1 (hK t ht)).1
    linarith
  -- so the first derivative leaves its tangent no faster than `K t²/2`, either way
  have hup1 : ∀ t ∈ Icc (0:ℝ) 1, φ' t - φ' 0 - t * φ'' 0 ≤ K * t ^ 2 / 2 :=
    aux_le_of_deriv_le (g := fun t => φ' t - φ' 0 - t * φ'' 0) (g' := fun t => φ'' t - φ'' 0)
      (fun t ht => ((hφ' t ht).sub_const _).sub (hid2 t)) hquad (by simp) hup2
  have hdn1 : ∀ t ∈ Icc (0:ℝ) 1, φ' 0 + t * φ'' 0 - φ' t ≤ K * t ^ 2 / 2 :=
    aux_le_of_deriv_le (g := fun t => φ' 0 + t * φ'' 0 - φ' t) (g' := fun t => φ'' 0 - φ'' t)
      (fun t ht => ((hid2 t).const_add (φ' 0)).sub (hφ' t ht)) hquad (by simp) hdn2
  -- so the value leaves its tangent-plus-curvature no faster than `K t³/6`, either way
  have hupper : φ 1 - φ 0 - φ' 0 - φ'' 0 / 2 ≤ K / 6 := by
    have h := aux_le_of_deriv_le (g := fun t => φ t - φ 0 - t * φ' 0 - t ^ 2 / 2 * φ'' 0)
      (g' := fun t => φ' t - φ' 0 - t * φ'' 0)
      (fun t ht => (((hφ t ht).sub_const _).sub (hid1 t)).sub (hquadhalf t))
      hcube (by simp) hup1 1 (right_mem_Icc.2 zero_le_one)
    norm_num at h
    linarith [h]
  have hlower : φ 0 + φ' 0 + φ'' 0 / 2 - φ 1 ≤ K / 6 := by
    have h := aux_le_of_deriv_le (g := fun t => φ 0 + t * φ' 0 + t ^ 2 / 2 * φ'' 0 - φ t)
      (g' := fun t => φ' 0 + t * φ'' 0 - φ' t)
      (fun t ht => (((hid1 t).const_add (φ 0)).add (hquadhalf t)).sub (hφ t ht))
      hcube (by simp) hdn1 1 (right_mem_Icc.2 zero_le_one)
    norm_num at h
    linarith [h]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- A map out of a coordinate space is its values on the standard basis. -/
theorem aux_clm_sum_single {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : Vec ℝ d →L[ℝ] G) (v : Vec ℝ d) : L v = ∑ j, v j • L (Pi.single j 1) := by
  conv_lhs => rw [show v = ∑ j, v j • (Pi.single j 1 : Vec ℝ d) from by
    ext k; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => map_smul _ _ _

/-- The same, at a codomain written out as one more `→L[ℝ]` rather than as a
generic `NormedAddCommGroup`: what `T`'s own type actually is, so unifying `G`
against it does not have to cross the diamond between the two. -/
theorem aux_clm_sum_single2 {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : Vec ℝ d →L[ℝ] Vec ℝ d →L[ℝ] H) (v : Vec ℝ d) :
    L v = ∑ j, v j • L (Pi.single j 1) := by
  conv_lhs => rw [show v = ∑ j, v j • (Pi.single j 1 : Vec ℝ d) from by
    ext k; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => map_smul _ _ _

/-- The thesis's `|z - z✱|ᵀ |Jᵢ| |z - z✱| ≤ γᵀ Mᵢ γ`: an entrywise bound on a
bilinear map is a bound on the quadratic form it takes at anything `γ` covers. -/
theorem aux_abs_quad_le (T : Vec ℝ d →L[ℝ] Vec ℝ d →L[ℝ] ℝ) (v γ : Vec ℝ d) (M : Mat ℝ d d)
    (hM : ∀ j k, |T (Pi.single j 1) (Pi.single k 1)| ≤ M j k) (hv : ∀ j, |v j| ≤ γ j) :
    |T v v| ≤ γ ⬝ᵥ (M *ᵥ γ) := by -- --- PROOF ---
  have hexp : T v v = ∑ j, ∑ k, v j * v k * T (Pi.single j 1) (Pi.single k 1) := by
    rw [aux_clm_sum_single T v, _root_.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [_root_.smul_apply, aux_clm_sum_single (T (Pi.single j 1)) v, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by simp [smul_eq_mul]; ring
  have hγ : ∀ j, 0 ≤ γ j := fun j => le_trans (abs_nonneg _) (hv j)
  rw [hexp]
  calc |∑ j, ∑ k, v j * v k * T (Pi.single j 1) (Pi.single k 1)|
      ≤ ∑ j, |∑ k, v j * v k * T (Pi.single j 1) (Pi.single k 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ k, γ j * (M j k * γ k) := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul, abs_mul]
        calc |v j| * |v k| * |T (Pi.single j 1) (Pi.single k 1)|
            ≤ γ j * γ k * M j k :=
              mul_le_mul (mul_le_mul (hv j) (hv k) (abs_nonneg _) (hγ j)) (hM j k)
                (abs_nonneg _) (mul_nonneg (hγ j) (hγ k))
          _ = γ j * (M j k * γ k) := by ring
    _ = γ ⬝ᵥ (M *ᵥ γ) := by simp [dotProduct, mulVec, Finset.mul_sum]

/-- `aux_abs_quad_le`, read once more at `T` with its first argument already
fixed: an entrywise bound on a trilinear map is a bound on the cubic form. -/
theorem aux_abs_cubic_le (T : Vec ℝ d →L[ℝ] Vec ℝ d →L[ℝ] Vec ℝ d →L[ℝ] ℝ) (v γ : Vec ℝ d)
    (M : Fin d → Mat ℝ d d)
    (hM : ∀ j k l, |T (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)| ≤ M j k l)
    (hv : ∀ j, |v j| ≤ γ j) :
    |T v v v| ≤ ∑ j, γ j * (γ ⬝ᵥ (M j *ᵥ γ)) := by -- --- PROOF ---
  have hγ : ∀ j, 0 ≤ γ j := fun j => le_trans (abs_nonneg _) (hv j)
  have hexp1 : T v v v = ∑ j, v j * (T (Pi.single j 1) v v) := by
    rw [aux_clm_sum_single2 T v, _root_.sum_apply, _root_.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [_root_.smul_apply, _root_.smul_apply, smul_eq_mul]
  have hstep : ∀ j, |T (Pi.single j 1) v v| ≤ γ ⬝ᵥ (M j *ᵥ γ) := fun j =>
    aux_abs_quad_le (T (Pi.single j 1)) v γ (M j) (fun k l => hM j k l) hv
  rw [hexp1]
  calc |∑ j, v j * (T (Pi.single j 1) v v)|
      ≤ ∑ j, |v j * (T (Pi.single j 1) v v)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |v j| * |T (Pi.single j 1) v v| := Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ ≤ ∑ j, γ j * (γ ⬝ᵥ (M j *ᵥ γ)) :=
        Finset.sum_le_sum fun j _ => mul_le_mul (hv j) (hstep j) (abs_nonneg _) (hγ j)

/-- The thesis's `max_{z ∈ Ẑ} |z - z✱| ≤ |c - z✱| + Σⱼ |g⁽ʲ⁾|`, which is the `γ`
that `lagrangeRemainder` computes. -/
theorem aux_abs_sub_le_radius (Z : Zonotope (Vec ℝ d)) (zs : Vec ℝ d) {z : Vec ℝ d}
    (hz : z ∈ Z.construct) (j : Fin d) :
    |z j - zs j| ≤ |Z.c j - zs j| + ∑ k, |Z.G k j| := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hz
  have hco : (Z.c + ∑ k, β k • Z.G k) j - zs j = Z.c j - zs j + ∑ k, β k * Z.G k j := by
    simp [Finset.sum_apply]
    ring
  have hsum : |∑ k, β k * Z.G k j| ≤ ∑ k, |Z.G k j| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hβ k)
  have := abs_add_le (Z.c j - zs j) (∑ k, β k * Z.G k j)
  rw [hco]
  linarith

/-- Stacking commutes with a difference, so the deviation of `(x, u)` from the
expansion point is the stacked pair of deviations. -/
theorem aux_append_sub (x xs : Vec ℝ n) (u us : Vec ℝ m) :
    Fin.append (x - xs) (u - us) = Fin.append x u - Fin.append xs us := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

/-- [1, Sec. 4.1] at one coordinate: what is left of `F` once its affine part
and its exact quadratic part at `zs` are subtracted is `γᵀ(Στ)γ/6`-shaped —
`aux_abs_remainder_le` (the order-one file) carried one order further. -/
theorem aux_abs_remainder_le2 {C : Set (Vec ℝ d)} (hC : Convex ℝ C) {F : Vec ℝ d → ℝ}
    {Ff : Vec ℝ d → (Vec ℝ d →L[ℝ] ℝ)} {Hf : Vec ℝ d → (Vec ℝ d →L[ℝ] Vec ℝ d →L[ℝ] ℝ)}
    {Ef : Vec ℝ d → (Vec ℝ d →L[ℝ] Vec ℝ d →L[ℝ] Vec ℝ d →L[ℝ] ℝ)}
    (hF : ∀ ξ ∈ C, HasFDerivAt F (Ff ξ) ξ) (hH : ∀ ξ ∈ C, HasFDerivAt Ff (Hf ξ) ξ)
    (hE : ∀ ξ ∈ C, HasFDerivAt Hf (Ef ξ) ξ)
    {M : Fin d → Mat ℝ d d}
    (hM : ∀ ξ ∈ C, ∀ j k l, |Ef ξ (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)| ≤ M j k l)
    {zs z γ : Vec ℝ d} (hzs : zs ∈ C) (hz : z ∈ C) (hγ : ∀ j, |z j - zs j| ≤ γ j) :
    |F z - F zs - Ff zs (z - zs) - Hf zs (z - zs) (z - zs) / 2|
      ≤ (∑ j, γ j * (γ ⬝ᵥ (M j *ᵥ γ))) / 6 := by -- --- PROOF ---
  set h : Vec ℝ d := z - zs with hh
  -- the segment from `zs` to `z`, and the state as `t` moves along it
  have hmem : ∀ t ∈ Icc (0:ℝ) 1, zs + t • h ∈ C := fun t ht => hC.add_smul_sub_mem hzs hz ht
  have hpath : ∀ t : ℝ, HasDerivAt (fun s : ℝ => zs + s • h) h t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const h).const_add zs
  have hφ : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => F (zs + s • h)) (Ff (zs + t • h) h) t := fun t ht =>
    (hF _ (hmem t ht)).comp_hasDerivAt t (hpath t)
  -- its first derivative along the segment, from the chain rule at `hH`
  have hφ' : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => Ff (zs + s • h) h) (Hf (zs + t • h) h h) t := by
    intro t ht
    have h3 := ((hH _ (hmem t ht)).clm_apply
      (hasFDerivAt_const h (zs + t • h))).comp_hasDerivAt t (hpath t)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      _root_.add_apply, _root_.zero_apply, map_zero, zero_add] at h3
    exact h3
  -- and the second, one `clm_apply` further, from `hE`
  have hφ'' : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => Hf (zs + s • h) h h) (Ef (zs + t • h) h h h) t := by
    intro t ht
    have h3 := (((hE _ (hmem t ht)).clm_apply (hasFDerivAt_const h (zs + t • h))).clm_apply
      (hasFDerivAt_const h (zs + t • h))).comp_hasDerivAt t (hpath t)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      _root_.add_apply, _root_.zero_apply, map_zero, zero_add] at h3
    exact h3
  -- the third derivative's cubic-form bound, at every point of the segment
  have hK : ∀ t ∈ Icc (0:ℝ) 1, |Ef (zs + t • h) h h h| ≤ ∑ j, γ j * (γ ⬝ᵥ (M j *ᵥ γ)) :=
    fun t ht => aux_abs_cubic_le _ _ _ _ (hM _ (hmem t ht)) hγ
  -- assembled by the cubic Taylor bound, then read back at the segment's ends
  have hfin := aux_abs_taylor_le2 hφ hφ' hφ'' hK
  rw [show zs + (1:ℝ) • h = z from by rw [hh]; simp] at hfin
  simpa using hfin


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.1]: where `A, B` are the derivative of `f` at `(xs, us)`, `Q` is
half the exact Hessian there and `E` bounds the third derivative entrywise,
`lagrangeRemainder` certifies the field with its quadratic part shifted out. -/
theorem AbstractionError.of_lagrange {f : Vec ℝ n → Vec ℝ m → Vec ℝ n} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {R : Set (Vec ℝ n)} {U : Set (Vec ℝ m)}
    {F : Vec ℝ (n + m) → Vec ℝ n} {C : Set (Vec ℝ (n + m))} {Z : Zonotope (Vec ℝ (n + m))}
    {Ff : Fin n → Vec ℝ (n + m) → (Vec ℝ (n + m) →L[ℝ] ℝ)}
    {Hf : Fin n → Vec ℝ (n + m) → (Vec ℝ (n + m) →L[ℝ] Vec ℝ (n + m) →L[ℝ] ℝ)}
    {Ef : Fin n → Vec ℝ (n + m) → (Vec ℝ (n + m) →L[ℝ] Vec ℝ (n + m) →L[ℝ] Vec ℝ (n + m) →L[ℝ] ℝ)}
    {E : Fin n → Fin (n + m) → Mat ℝ (n + m) (n + m)} {Q : Fin n → Mat ℝ (n + m) (n + m)}
    (hf : ∀ x u, F (Fin.append x u) = f x u) (hC : Convex ℝ C)
    (hzs : Fin.append xs us ∈ C) (hZC : Z.construct ⊆ C)
    (hZ : ∀ x ∈ R, ∀ u ∈ U, Fin.append x u ∈ Z.construct)
    (hF : ∀ i, ∀ ξ ∈ C, HasFDerivAt (fun z => F z i) (Ff i ξ) ξ)
    (hH : ∀ i, ∀ ξ ∈ C, HasFDerivAt (Ff i) (Hf i ξ) ξ)
    (hE : ∀ i, ∀ ξ ∈ C, HasFDerivAt (Hf i) (Ef i ξ) ξ)
    (hEb : ∀ i, ∀ ξ ∈ C, ∀ j k l,
      |Ef i ξ (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)| ≤ E i j k l)
    -- `A, B` pin `Ff` at `zs`, as in the order-one file; `hQ` pins `Hf` there too
    (hA : ∀ i (v : Vec ℝ n) (w : Vec ℝ m),
      Ff i (Fin.append xs us) (Fin.append v w) = (A *ᵥ v) i + (B *ᵥ w) i)
    (hQ : ∀ i (v : Vec ℝ (n + m)), Hf i (Fin.append xs us) v v = 2 * (v ⬝ᵥ (Q i *ᵥ v))) :
    AbstractionError (S := ℐ𝒱)
      (fun x u => f x u -
        (fun i => Fin.append (x - xs) (u - us) ⬝ᵥ (Q i *ᵥ Fin.append (x - xs) (u - us))))
      A B xs us R U (lagrangeRemainder E Z (Fin.append xs us)) where
  encloses x hx u hu := by
    intro i
    have hzZ := hZ x hx u hu
    have hbnd := aux_abs_remainder_le2 hC (hF i) (hH i) (hE i) (hEb i) hzs (hZC hzZ)
      (fun j => aux_abs_sub_le_radius Z _ hzZ j)
    -- the stacked derivative read back as the two Jacobian blocks and `Q`
    rw [← aux_append_sub, hA i, hQ i, hf, hf] at hbnd
    have habs := abs_le.1 hbnd
    -- the quadratic term at `xs, us` itself is the zero vector's, hence zero
    have hz : Fin.append ((xs : Vec ℝ n) - xs) ((us : Vec ℝ m) - us) = (0 : Vec ℝ (n + m)) := by
      rw [aux_append_sub]; exact sub_self _
    have hzero : Fin.append ((xs : Vec ℝ n) - xs) ((us : Vec ℝ m) - us)
        ⬝ᵥ (Q i *ᵥ Fin.append (xs - xs) (us - us)) = 0 := by rw [hz]; simp
    -- the two directions of the box membership, read entrywise back into `ℝ`
    refine ⟨?_, ?_⟩ <;>
      rw [Entrywise.entry_vec, Entrywise.entry_vec] <;>
      simp only [lagrangeRemainder, Pi.sub_apply, Pi.add_apply, Pi.neg_apply] <;>
      linarith [habs.1, habs.2, hzero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
