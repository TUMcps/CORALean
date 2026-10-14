module

public import CORALean.ContSet.Zonotope.Real.Operations.QuadMapInt
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

@[expose] public section

/-!
# `quadint` is `quad` at the midpoints plus a box

[1, Thm. 1]: with `H = Hc ⊕ [-HΔ, HΔ]`, `quadint(H, Z) = quad(Hc, Z) ⊕ [-η, η]`,
`ηᵢ = |Z|ᵀ HΔ⁽ⁱ⁾ |Z|`, `|Z| = |c| + Σⱼ |g⁽ʲ⁾|` ([1, Eq. 7], `Zonotope.absBound`). The two are
equal as zonotopes, the box `[-η, η]` being `Interval.zonotope`, centre `0` and axis
generators `η`.

The content is the identity `d_Δ + Σᵢ h_Δ⁽ⁱ⁾ = η`: the radii of the interval centre and
generators add up to `Σⱼ Σₖ |λ⁽ʲ⁾|ᵀ HΔ |λ⁽ᵏ⁾|` over all centre and generator pairs, the
printed proof's last display, which is `|Z|ᵀ HΔ |Z|`. The centre's `½ Σ |g|ᵀHΔ|g|` and the
square generators' `½ |g|ᵀHΔ|g|` make the diagonal whole, the linear generators carry the
centre-generator pairs both ways, and the pair generators the generator pairs both ways.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `b(u + Σ vⱼ, u + Σ vⱼ)` expanded: constant, linear, and every ordered pair. -/
theorem Zonotope.aux_quadMapInt_sq {h : ℕ} (b : LinearMap.BilinForm ℝ (Vec ℝ n)) (u : Vec ℝ n)
    (v : Fin h → Vec ℝ n) :
    b (u + ∑ j, v j) (u + ∑ j, v j)
      = b u u + ∑ j, (b u (v j) + b (v j) u) + ∑ j, ∑ k, b (v j) (v k) := by -- --- PROOF ---
  simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply]
  simp only [Finset.sum_add_distrib]
  have hc : ∑ x, ∑ c, b (v c) (v x) = ∑ j, ∑ k, b (v j) (v k) := Finset.sum_comm
  rw [hc]
  ring

/-- The ordered pairs split into the diagonal and one term per unordered pair `j < k`. -/
theorem Zonotope.aux_quadMapInt_diagpair {h : ℕ} (f : Fin h → Fin h → ℝ) :
    ∑ j, ∑ k, f j k
      = ∑ j, f j j + ∑ j, ∑ k, (if j < k then f j k + f k j else 0) := by -- --- PROOF ---
  have hswap : ∑ j : Fin h, ∑ k, (if j < k then f k j else 0)
      = ∑ j : Fin h, ∑ k, (if k < j then f j k else 0) := by
    rw [Finset.sum_comm]
  have hite : ∀ j k : Fin h, (if j < k then f j k + f k j else 0)
      = (if j < k then f j k else 0) + (if j < k then f k j else 0) := fun j k => by
    split_ifs <;> ring
  simp only [hite, Finset.sum_add_distrib, hswap]
  -- every `(j, k)` is diagonal, `j < k` or `j > k`, exactly once
  have hdiag : ∀ j k : Fin h, f j k = (if j = k then f j k else 0)
      + (if j < k then f j k else 0) + (if k < j then f j k else 0) := fun j k => by
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · rw [if_neg hjk.ne, if_pos hjk, if_neg (asymm hjk)]; ring
    · subst hjk; rw [if_pos rfl, if_neg (lt_irrefl j)]; ring
    · rw [if_neg hjk.ne', if_neg (asymm hjk), if_pos hjk]; ring
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hdiag j k]
  simp only [Finset.sum_add_distrib]
  rw [show (∑ j : Fin h, ∑ k, (if j = k then f j k else 0)) = ∑ j, f j j from
    Finset.sum_congr rfl fun j _ =>
      (Finset.sum_eq_single j (fun k _ hk => if_neg (Ne.symm hk))
        (fun hj => absurd (Finset.mem_univ j) hj)).trans (if_pos rfl)]
  ring

/-- The pair block, read over `Fin (h * h)` through `finProdFinEquiv`. -/
theorem Zonotope.aux_quadMapInt_pairblock {h : ℕ} (f : Fin h → Fin h → ℝ) :
    ∑ l : Fin (h * h), f (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2
      = ∑ j, ∑ k, f j k := by
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun jk : Fin h × Fin h => f jk.1 jk.2)
    fun _ => rfl]
  exact Fintype.sum_prod_type _

/-- The radii add up to `|Z|ᵀ HΔ⁽ⁱ⁾ |Z|`: the identity behind [1, Thm. 1]. -/
theorem Zonotope.aux_quadMapInt_radius (HΔ : Fin m → Mat ℝ n n) (Z : Zonotope (Vec ℝ n))
    (i : Fin m) :
    ((⟨Z.h, fun i => |Z.c i|, fun j i => |Z.G j i|⟩ : Zonotope (Vec ℝ n)).quadMap HΔ).c i
      + ∑ l : Fin (Z.h + Z.h + Z.h * Z.h),
          ((⟨Z.h, fun i => |Z.c i|, fun j i => |Z.G j i|⟩ : Zonotope (Vec ℝ n)).quadMap HΔ).G l i
      = Z.absBound ⬝ᵥ (HΔ i *ᵥ Z.absBound) := by -- --- PROOF ---
  set u : Vec ℝ n := fun i => |Z.c i| with hu
  set v : Fin Z.h → Vec ℝ n := fun j i => |Z.G j i| with hv
  set b := Matrix.toBilin' (HΔ i) with hbdef
  have hb : ∀ x y : Vec ℝ n, x ⬝ᵥ (HΔ i *ᵥ y) = b x y := fun x y => by
    rw [hbdef, Matrix.toBilin'_apply']
  -- `|Z|` is the absolute centre plus the absolute generators
  have habs : Z.absBound = u + ∑ j, v j := by
    funext k
    simp [Zonotope.absBound, hu, hv, Finset.sum_apply]
  rw [habs, hb, Zonotope.aux_quadMapInt_sq, Zonotope.aux_quadMapInt_diagpair]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Zonotope.quadMap]
  simp only [Fin.append_left, Fin.append_right, hb]
  -- the pair block guards its own terms, read back over all `(j, k)`
  rw [Zonotope.aux_quadMapInt_pairblock (fun j k =>
    (if j < k then b (v j) (v k) + b (v k) (v j) else 0))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: `quadint(H, Z) = quad(Hc, Z) ⊕ [-η, η]`, `ηᵢ = |Z|ᵀ HΔ⁽ⁱ⁾ |Z|`. -/
theorem Zonotope.quadMapInt_eq (Hc HΔ : Fin m → Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    Z.quadMapInt Hc HΔ = (Z.quadMap Hc).plus
      (Interval.zonotope ⟨fun i => -(Z.absBound ⬝ᵥ (HΔ i *ᵥ Z.absBound)),
        fun i => Z.absBound ⬝ᵥ (HΔ i *ᵥ Z.absBound)⟩) := by -- --- PROOF ---
  simp only [Zonotope.quadMapInt, Zonotope.plus, Interval.zonotope, Zonotope.mk.injEq,
    true_and]
  refine ⟨by funext i; simp, heq_of_eq ?_⟩
  congr 1
  -- each axis generator carries the summed radius, which is `η`
  funext k i
  rw [Pi.single_apply]
  split_ifs with hik
  · subst hik
    simp only [Pi.add_apply, Finset.sum_apply]
    rw [show ∀ a : ℝ, (a - -a) / 2 = a from fun a => by ring]
    exact Zonotope.aux_quadMapInt_radius HΔ Z i
  · rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
