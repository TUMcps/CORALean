module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestDot
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
public import CORALean.ContSet.Ellipsoid.Real.Theorems.QMemConstruct
public import CORALean.Global.NearestPointSeparates
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section

/-!
# The distance between two ellipsoids

[1, Sec. II (distances)]: `dist(E(q₁, Q₁), E(q₂, Q₂)) =
max_{⟨l, l⟩ = 1} (⟨l, q₁⟩ - ⟨l, Q₁ l⟩^{1/2} - ⟨l, q₂⟩ - ⟨l, Q₂ l⟩^{1/2})`, the gap between
the least value of `lᵀ x` on the first and the largest on the second. For disjoint ellipsoids
the maximum is the Euclidean distance: the nearest point `p = y₀ - x₀` of the compact convex set
`E₂ - E₁` to the origin gives the direction `-p/‖p‖₂` attaining it. For intersecting ellipsoids
every value is `≤ 0`; touching ones give `0`, not the negative value the paper states
[1, Sec. II (sign of the distance)].

## References

* [1] A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". In Proc. of the 45th
      IEEE Conference on Decision and Control (CDC), pp. 1498-1503, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `‖-x‖₂ = ‖x‖₂`. -/
theorem aux_norm₂_neg (x : Vec ℝ n) : ‖-x‖₂ = ‖x‖₂ := by
  rw [show -x = (-1 : ℝ) • x by simp, norm₂_smul]
  simp

/-- The least value of `lᵀ x` on an ellipsoid, from the largest of `-lᵀ x`. -/
theorem aux_isLeast_dot (E : Ellipsoid n) (l : Vec ℝ n) :
    IsLeast ((l ⬝ᵥ ·) '' E.construct) (l ⬝ᵥ E.q - √(l ⬝ᵥ (E.Q *ᵥ l))) := by -- --- PROOF ---
  obtain ⟨⟨x, hx, hxv⟩, hub⟩ := E.isGreatest_dot (-l)
  have hsq : (-l) ⬝ᵥ (E.Q *ᵥ -l) = l ⬝ᵥ (E.Q *ᵥ l) := by
    rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [hsq, neg_dotProduct] at hxv hub
  refine ⟨⟨x, hx, ?_⟩, ?_⟩
  · simp only [neg_dotProduct] at hxv
    show l ⬝ᵥ x = _
    linarith
  · rintro _ ⟨y, hy, rfl⟩
    have := hub ⟨y, hy, rfl⟩
    simp only [neg_dotProduct] at this
    show _ ≤ l ⬝ᵥ y
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.dist_ellipsoid_eq_max (E₁ E₂ : Ellipsoid n) : -- --- STMT ---
    (Disjoint E₁.construct E₂.construct → ∃ d > 0,
      IsLeast {t | ∃ x ∈ E₁.construct, ∃ y ∈ E₂.construct, t = ‖x - y‖₂} d ∧
      IsGreatest {t | ∃ l : Vec ℝ n, ‖l‖₂ = 1 ∧ t = l ⬝ᵥ E₁.q - √(l ⬝ᵥ (E₁.Q *ᵥ l)) -
        l ⬝ᵥ E₂.q - √(l ⬝ᵥ (E₂.Q *ᵥ l))} d) ∧
    ((E₁.construct ∩ E₂.construct).Nonempty → ∀ l : Vec ℝ n,
      l ⬝ᵥ E₁.q - √(l ⬝ᵥ (E₁.Q *ᵥ l)) - l ⬝ᵥ E₂.q - √(l ⬝ᵥ (E₂.Q *ᵥ l)) ≤
        0) := by -- --- PROOF ---
  refine ⟨fun hdisj => ?_, fun ⟨z, hz1, hz2⟩ l => ?_⟩
  · -- the origin is not in `E₂ - E₁`, a compact convex set
    set K := E₂.construct + -E₁.construct with hK
    have hmemK : ∀ x ∈ E₁.construct, ∀ y ∈ E₂.construct, y - x ∈ K := fun x hx y hy =>
      ⟨y, hy, -x, by simpa using hx, (sub_eq_add_neg y x).symm⟩
    have h0 : (0 : Vec ℝ n) ∉ K := by
      rintro ⟨y, hy, z, hz, hyz⟩
      have hx : -z ∈ E₁.construct := by simpa using hz
      have : y = -z := eq_neg_of_add_eq_zero_left hyz
      exact Set.disjoint_left.mp hdisj hx (this ▸ hy)
    obtain ⟨p, hp, hd, hleast, hsep⟩ := nearest_point_separates K
      (E₂.isCompact_construct.add E₁.isCompact_construct.neg).isClosed
      (E₂.convex_construct.add E₁.convex_construct.neg) ⟨_, hmemK _ E₁.q_mem_construct _
        E₂.q_mem_construct⟩ 0 h0
    obtain ⟨y₀, hy₀, z₀, hz₀, rfl⟩ := hp
    have hx₀ : -z₀ ∈ E₁.construct := by simpa using hz₀
    simp only [zero_sub] at hd hleast hsep
    rw [aux_norm₂_neg] at hd
    -- every pair is at least `‖p‖₂` apart, so `lᵀ x - lᵀ y ≥ ‖p‖₂` along `l = -p/‖p‖₂`
    have hgap : ∀ x ∈ E₁.construct, ∀ y ∈ E₂.construct,
        (y₀ + z₀) ⬝ᵥ (y₀ + z₀) ≤ (y₀ + z₀) ⬝ᵥ (y - x) := fun x hx y hy => by
      have := hsep _ (hmemK x hx y hy)
      rw [neg_dotProduct, neg_dotProduct] at this
      linarith
    set d := ‖y₀ + z₀‖₂ with hdd
    have hpp : (y₀ + z₀) ⬝ᵥ (y₀ + z₀) = d ^ 2 := dotProduct_self _
    set l := -(d⁻¹ • (y₀ + z₀)) with hl
    have hlx : ∀ x ∈ E₁.construct, ∀ y ∈ E₂.construct, d ≤ l ⬝ᵥ x - l ⬝ᵥ y :=
      fun x hx y hy => by
        have hg := hgap x hx y hy
        rw [dotProduct_sub, hpp] at hg
        have hl' : l ⬝ᵥ x - l ⬝ᵥ y = d⁻¹ * ((y₀ + z₀) ⬝ᵥ y - (y₀ + z₀) ⬝ᵥ x) := by
          rw [hl, neg_dotProduct, neg_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
            smul_eq_mul]
          ring
        rw [hl', le_inv_mul_iff₀ hd]
        nlinarith
    -- `d` is the least distance, attained at `(-z₀, y₀)`, and `l` is a unit vector
    refine ⟨d, hd, ⟨⟨-z₀, hx₀, y₀, hy₀, ?_⟩, ?_⟩, ⟨⟨l, ?_, ?_⟩, ?_⟩⟩
    · rw [hdd, show -z₀ - y₀ = -(y₀ + z₀) by abel, aux_norm₂_neg]
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      have h' : ‖-(y₀ + z₀)‖₂ ≤ ‖-(y - x)‖₂ := hleast.2 ⟨y - x, hmemK x hx y hy, rfl⟩
      rw [aux_norm₂_neg, aux_norm₂_neg] at h'
      rw [show x - y = -(y - x) by abel, aux_norm₂_neg]
      exact h'
    · rw [hl, aux_norm₂_neg, norm₂_smul, abs_of_pos (inv_pos.mpr hd), inv_mul_cancel₀ hd.ne']
    -- the gap between the extreme values is attained at `x₀ = -z₀`, `y₀`
    · obtain ⟨⟨x, hx, hxv⟩, hxl⟩ := aux_isLeast_dot E₁ l
      obtain ⟨⟨y, hy, hyv⟩, hyg⟩ := E₂.isGreatest_dot l
      simp only at hxv hyv
      have h1 := hlx x hx y hy
      have h2 := hxl ⟨-z₀, hx₀, rfl⟩
      have h3 := hyg ⟨y₀, hy₀, rfl⟩
      simp only at h2 h3
      have h4 : l ⬝ᵥ (-z₀) - l ⬝ᵥ y₀ = d := by
        rw [← dotProduct_sub, show -z₀ - y₀ = -(y₀ + z₀) by abel, hl, neg_dotProduct,
          dotProduct_neg, neg_neg, smul_dotProduct, hpp, smul_eq_mul]
        field_simp
      linarith
    -- any unit direction: Cauchy–Schwarz along `-z₀ - y₀`
    · rintro _ ⟨l', hl', rfl⟩
      have h2 := (aux_isLeast_dot E₁ l').2 ⟨-z₀, hx₀, rfl⟩
      have h3 := (E₂.isGreatest_dot l').2 ⟨y₀, hy₀, rfl⟩
      simp only at h2 h3
      have hcs := dotProduct_le_norm₂_mul_norm₂ l' (-z₀ - y₀)
      rw [hl', one_mul, show -z₀ - y₀ = -(y₀ + z₀) by abel, aux_norm₂_neg, dotProduct_neg] at hcs
      rw [dotProduct_neg] at h2
      have : l' ⬝ᵥ (y₀ + z₀) = l' ⬝ᵥ y₀ + l' ⬝ᵥ z₀ := dotProduct_add _ _ _
      linarith
  · have h1 := (aux_isLeast_dot E₁ l).2 ⟨z, hz1, rfl⟩
    have h2 := (E₂.isGreatest_dot l).2 ⟨z, hz2, rfl⟩
    simp only at h1 h2
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
