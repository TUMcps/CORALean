module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestDot
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
public import CORALean.ContSet.Ellipsoid.Real.Theorems.QMemConstruct
public import CORALean.Global.NearestPointSeparates

@[expose] public section

/-!
# The distance from a point to an ellipsoid

[1, Sec. II (distances)]: `dist(E(q, Q), a) = max_{⟨l, l⟩ = 1} (⟨l, a⟩ - ⟨l, q⟩ - ⟨l, Q l⟩^{1/2})`.
For `a ∉ E` the maximum is the Euclidean distance, attained in the direction of `a` from its
nearest point; for `a ∈ E` every value is `≤ 0`. The paper says the value is negative inside the
ellipsoid [1, Sec. II (sign of the distance)], which fails on the boundary, where it is `0`
(`dist_point_nonneg_counterexample`).

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

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.dist_point_eq_max (E : Ellipsoid n) (a : Vec ℝ n) :
    (a ∉ E.construct → ∃ d > 0, IsLeast ((fun x => ‖a - x‖₂) '' E.construct) d ∧
      IsGreatest {t | ∃ l : Vec ℝ n, ‖l‖₂ = 1 ∧
        t = l ⬝ᵥ a - l ⬝ᵥ E.q - √(l ⬝ᵥ (E.Q *ᵥ l))} d) ∧
    (a ∈ E.construct → ∀ l : Vec ℝ n, l ⬝ᵥ a - l ⬝ᵥ E.q - √(l ⬝ᵥ (E.Q *ᵥ l)) ≤
      0) := by -- --- PROOF ---
  refine ⟨fun ha => ?_, fun ha l => ?_⟩
  · obtain ⟨p, hp, hd, hleast, hsep⟩ := nearest_point_separates E.construct
      E.isClosed_construct E.convex_construct ⟨_, E.q_mem_construct⟩ a ha
    refine ⟨‖a - p‖₂, hd, hleast, ⟨⟨‖a - p‖₂⁻¹ • (a - p), ?_, ?_⟩, ?_⟩⟩
    · rw [norm₂_smul, abs_of_pos (inv_pos.mpr hd), inv_mul_cancel₀ hd.ne']
    -- at `l = (a - p)/d` the maximum over `E` is taken at `p`
    · set l := ‖a - p‖₂⁻¹ • (a - p) with hl
      obtain ⟨⟨x, hx, hxval⟩, hub⟩ := E.isGreatest_dot l
      have hρ : l ⬝ᵥ E.q + √(l ⬝ᵥ (E.Q *ᵥ l)) = l ⬝ᵥ p := by
        refine le_antisymm ?_ (hub ⟨p, hp, rfl⟩)
        rw [← hxval]
        show l ⬝ᵥ x ≤ l ⬝ᵥ p
        rw [hl, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hsep x hx) (inv_nonneg.mpr hd.le)
      have : l ⬝ᵥ a - l ⬝ᵥ p = ‖a - p‖₂ := by
        rw [← dotProduct_sub, hl, smul_dotProduct, dotProduct_self, smul_eq_mul]
        field_simp
      linarith
    -- any direction: `lᵀ a - ρ(l) ≤ lᵀ (a - p) ≤ ‖a - p‖₂`
    · rintro _ ⟨l, hl1, rfl⟩
      have hlp := (E.isGreatest_dot l).2 ⟨p, hp, rfl⟩
      have hcs := dotProduct_le_norm₂_mul_norm₂ l (a - p)
      rw [hl1, one_mul, dotProduct_sub] at hcs
      simp only at hlp
      linarith
  · have := (E.isGreatest_dot l).2 ⟨a, ha, rfl⟩
    simp only at this
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
