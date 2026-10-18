module

public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstractionError
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLin
public import CORALean.ContSet.Interval.Real.Instances
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# A twice-differentiable field supplies its own certificate

[1, Prop. 1], and the one place in the directory where `f` is differentiated:
`abstrErrLin` is an `AbstractionError` once `A` and `B` really are the derivative
at `(xs, us)` and `H` really bounds the second derivative. No theorem that
*spends* a certificate imports it, so `AbstractionError` and the reachability
chain built on it stay derivative-free: a caller holding a bound from elsewhere
never meets any of this.

`C` carries the regularity the printed proposition leaves implicit: the two
`HasFDerivAt` hypotheses are two-sided at every point of it, so `C` is read as an
open convex neighbourhood of `Z` and of the expansion point, and the segment
`Z ∪ {zs}` spans lies inside it, the segment of `ξ(z, z✱)` in [1, Eq. 2]'s remainder.

`hA` pins `Ff i zs` on every stacked vector, which is what makes `A` and `B` the
Jacobian blocks rather than merely one pair among many. The parameter box `P` of
the proposition has no counterpart: `AbstractionError` carries no parameters, so
the bound is over states and inputs alone.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

/-- Taylor at order one with the remainder bounded rather than evaluated: no
mean value is named, so `φ''` is never asked for at an unknown point. -/
theorem aux_abs_taylor_le {φ φ' φ'' : ℝ → ℝ} {K : ℝ}
    (hφ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt φ' (φ'' t) t)
    (hK : ∀ t ∈ Icc (0:ℝ) 1, |φ'' t| ≤ K) : -- --- STMT ---
    |φ 1 - φ 0 - φ' 0| ≤ K / 2 := by -- --- PROOF ---
  have hlin : ∀ s : ℝ, HasDerivAt (fun t : ℝ => K * t) K s := fun s => by
    simpa using (hasDerivAt_id s).const_mul K
  have hid : ∀ s : ℝ, HasDerivAt (fun t : ℝ => t * φ' 0) (φ' 0) s := fun s => by
    simpa using (hasDerivAt_id s).mul_const (φ' 0)
  have hquad : ∀ s : ℝ, HasDerivAt (fun t : ℝ => K * t ^ 2 / 2) (K * s) s := fun s => by
    have h := ((hasDerivAt_pow 2 s).const_mul K).div_const 2
    norm_num at h
    rwa [show K * (2 * s) / 2 = K * s by ring] at h
  -- the slope leaves `φ' 0` no faster than `K`, in either direction
  have hup : ∀ t ∈ Icc (0:ℝ) 1, φ' t - φ' 0 ≤ K * t :=
    aux_le_of_deriv_le (fun t ht => (hφ' t ht).sub_const _) hlin (by simp)
      (fun t ht => (abs_le.1 (hK t ht)).2)
  have hdn : ∀ t ∈ Icc (0:ℝ) 1, φ' 0 - φ' t ≤ K * t := by
    refine aux_le_of_deriv_le (g := fun t => φ' 0 - φ' t) (g' := fun t => -φ'' t)
      (fun t ht => (hφ' t ht).const_sub (φ' 0)) hlin (by simp) (fun t ht => ?_)
    have := (abs_le.1 (hK t ht)).1
    linarith
  -- so the value leaves its tangent no faster than `K t²/2`, in either direction
  have hupper : φ 1 - φ 0 - φ' 0 ≤ K / 2 := by
    have := aux_le_of_deriv_le (g := fun t => φ t - φ 0 - t * φ' 0)
      (g' := fun t => φ' t - φ' 0) (fun t ht => ((hφ t ht).sub_const _).sub (hid t))
      hquad (by simp) hup 1 (right_mem_Icc.2 zero_le_one)
    simpa using this
  have hlower : φ 0 + φ' 0 - φ 1 ≤ K / 2 := by
    have := aux_le_of_deriv_le (g := fun t => φ 0 + t * φ' 0 - φ t)
      (g' := fun t => φ' 0 - φ' t) (fun t ht => ((hid t).const_add (φ 0)).sub (hφ t ht))
      hquad (by simp) hdn 1 (right_mem_Icc.2 zero_le_one)
    simpa using this
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- A map out of a coordinate space is its values on the standard basis. -/
theorem aux_clm_sum_single {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : Vec ℝ d →L[ℝ] G) (v : Vec ℝ d) : L v = ∑ j, v j • L (Pi.single j 1) := by
  conv_lhs => rw [show v = ∑ j, v j • (Pi.single j 1 : Vec ℝ d) from by
    ext k; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => map_smul _ _ _

/-- The thesis's `|z - z✱|ᵀ |Jᵢ| |z - z✱| ≤ γᵀ Mᵢ γ`: an entrywise bound on a
bilinear map is a bound on the quadratic form it takes at anything `γ` covers. -/
theorem aux_abs_quad_le (T : Vec ℝ d →L[ℝ] Vec ℝ d →L[ℝ] ℝ) (v γ : Vec ℝ d) (M : Mat ℝ d d)
    (hM : ∀ j k, |T (Pi.single j 1) (Pi.single k 1)| ≤ M j k) (hv : ∀ j, |v j| ≤ γ j) :
    |T v v| ≤ γ ⬝ᵥ (M *ᵥ γ) := by -- --- PROOF ---
  -- the form written out on the basis, which is where the entries appear
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
        -- three nonnegative factors, each replaced by what bounds it
        rw [abs_mul, abs_mul]
        calc |v j| * |v k| * |T (Pi.single j 1) (Pi.single k 1)|
            ≤ γ j * γ k * M j k :=
              mul_le_mul (mul_le_mul (hv j) (hv k) (abs_nonneg _) (hγ j)) (hM j k)
                (abs_nonneg _) (mul_nonneg (hγ j) (hγ k))
          _ = γ j * (M j k * γ k) := by ring
    _ = γ ⬝ᵥ (M *ᵥ γ) := by simp [dotProduct, mulVec, Finset.mul_sum]

/-- [1, Prop. 1] at one coordinate: what is left of `F` once its affine part at
`zs` is subtracted is `γᵀ M γ / 2`, over any `z` that `γ` covers. -/
theorem aux_abs_remainder_le {C : Set (Vec ℝ d)} (hC : Convex ℝ C) {F : Vec ℝ d → ℝ}
    {Ff : Vec ℝ d → (Vec ℝ d →L[ℝ] ℝ)}
    {Hf : Vec ℝ d → (Vec ℝ d →L[ℝ] Vec ℝ d →L[ℝ] ℝ)}
    (hF : ∀ ξ ∈ C, HasFDerivAt F (Ff ξ) ξ) (hH : ∀ ξ ∈ C, HasFDerivAt Ff (Hf ξ) ξ)
    {M : Mat ℝ d d} (hM : ∀ ξ ∈ C, ∀ j k, |Hf ξ (Pi.single j 1) (Pi.single k 1)| ≤ M j k)
    {zs z γ : Vec ℝ d} (hzs : zs ∈ C) (hz : z ∈ C) (hγ : ∀ j, |z j - zs j| ≤ γ j) : -- --- STMT ---
    |F z - F zs - Ff zs (z - zs)| ≤ γ ⬝ᵥ (M *ᵥ γ) / 2 := by -- --- PROOF ---
  set h : Vec ℝ d := z - zs with hh
  -- the segment stays inside `C`, which is where both derivatives live
  have hmem : ∀ t ∈ Icc (0:ℝ) 1, zs + t • h ∈ C := fun t ht => hC.add_smul_sub_mem hzs hz ht
  have hpath : ∀ t : ℝ, HasDerivAt (fun s : ℝ => zs + s • h) h t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const h).const_add zs
  have hφ : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => F (zs + s • h)) (Ff (zs + t • h) h) t := fun t ht =>
    (hF _ (hmem t ht)).comp_hasDerivAt t (hpath t)
  -- the second derivative along the segment, the direction held constant
  have hφ' : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => Ff (zs + s • h) h) (Hf (zs + t • h) h h) t := by
    intro t ht
    have h3 := ((hH _ (hmem t ht)).clm_apply
      (hasFDerivAt_const h (zs + t • h))).comp_hasDerivAt t (hpath t)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      _root_.add_apply, _root_.zero_apply, map_zero, zero_add] at h3
    exact h3
  have hK : ∀ t ∈ Icc (0:ℝ) 1, |Hf (zs + t • h) h h| ≤ γ ⬝ᵥ (M *ᵥ γ) := fun t ht =>
    aux_abs_quad_le _ _ _ _ (hM _ (hmem t ht)) hγ
  have hfin := aux_abs_taylor_le hφ hφ' hK
  rw [show zs + (1:ℝ) • h = z from by rw [hh]; simp] at hfin
  simpa using hfin

/-- The thesis's `max_{z ∈ Ẑ} |z - z✱| ≤ |c - z✱| + Σⱼ |g⁽ʲ⁾|`, which is the `γ`
that `abstrErrLin` computes. -/
theorem aux_abs_sub_le_radius (Z : Zonotope (Vec ℝ d)) (zs : Vec ℝ d) {z : Vec ℝ d}
    (hz : z ∈ Z.construct) (j : Fin d) :
    |z j - zs j| ≤ |Z.c j - zs j| + ∑ k, |Z.G k j| := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hz
  have hco : (Z.c + ∑ k, β k • Z.G k) j - zs j = Z.c j - zs j + ∑ k, β k * Z.G k j := by
    simp [Finset.sum_apply]
    ring
  -- every coefficient is at most one, so each generator contributes its own size
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: where `A` and `B` are the derivative of `f` at `(xs, us)` and
`H` bounds its second derivative entrywise, `abstrErrLin` is a certificate. -/
theorem AbstractionError.of_hessian {f : Vec ℝ n → Vec ℝ m → Vec ℝ n} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {R : Set (Vec ℝ n)} {U : Set (Vec ℝ m)}
    {F : Vec ℝ (n + m) → Vec ℝ n} {C : Set (Vec ℝ (n + m))} {Z : Zonotope (Vec ℝ (n + m))}
    {Ff : Fin n → Vec ℝ (n + m) → (Vec ℝ (n + m) →L[ℝ] ℝ)}
    {Hf : Fin n → Vec ℝ (n + m) → (Vec ℝ (n + m) →L[ℝ] Vec ℝ (n + m) →L[ℝ] ℝ)}
    {H : Fin n → Mat ℝ (n + m) (n + m)}
    (hf : ∀ x u, F (Fin.append x u) = f x u) (hC : Convex ℝ C)
    (hzs : Fin.append xs us ∈ C) (hZC : Z.construct ⊆ C)
    (hZ : ∀ x ∈ R, ∀ u ∈ U, Fin.append x u ∈ Z.construct)
    (hF : ∀ i, ∀ ξ ∈ C, HasFDerivAt (fun z => F z i) (Ff i ξ) ξ)
    (hH : ∀ i, ∀ ξ ∈ C, HasFDerivAt (Ff i) (Hf i ξ) ξ)
    (hHb : ∀ i, ∀ ξ ∈ C, ∀ j k, |Hf i ξ (Pi.single j 1) (Pi.single k 1)| ≤ H i j k)
    (hA : ∀ i (v : Vec ℝ n) (w : Vec ℝ m),
      Ff i (Fin.append xs us) (Fin.append v w) = (A *ᵥ v) i + (B *ᵥ w) i) :
    AbstractionError (S := ℐ𝒱) f A B xs us R U (abstrErrLin H Z (Fin.append xs us)) where
  encloses x hx u hu := by
    -- the radius `abstrErrLin` takes its bound at
    set γ : Vec ℝ (n + m) := fun j => |Z.c j - Fin.append xs us j| + ∑ k, |Z.G k j| with hγ
    intro i
    have hzZ := hZ x hx u hu
    have hbnd := aux_abs_remainder_le hC (hF i) (hH i) (hHb i) hzs (hZC hzZ)
      (fun j => aux_abs_sub_le_radius Z _ hzZ j)
    -- the stacked derivative read back as the two Jacobian blocks
    rw [← aux_append_sub, hA i, hf, hf] at hbnd
    have habs := abs_le.1 hbnd
    refine ⟨?_, ?_⟩
    · show -(γ ⬝ᵥ (H i *ᵥ γ) / 2) ≤ f x u i - (f xs us i + (A *ᵥ (x - xs)) i + (B *ᵥ (u - us)) i)
      linarith [habs.1]
    · show f x u i - (f xs us i + (A *ᵥ (x - xs)) i + (B *ᵥ (u - us)) i) ≤ γ ⬝ᵥ (H i *ᵥ γ) / 2
      linarith [habs.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
