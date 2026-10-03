import CORALean.ContSet.HPolytope.Real.Theorems.PolyNormLeIff
import CORALean.ContSet.HPolytope.Real.Operations.RowLin
import CORALean.Global.EllipsotopeSupport

/-!
# An ellipsotope's distance from a zonotope, facet by facet

`[1, Eq. 11]`: for an ellipsotope inbody `E_p(G, c)` and a non-degenerate
zonotope circumbody `Ẑ = d + Z(H)` with facets `{Λ x ≤ b}` of `Z(H)`, the containment
radius is a maximum over facets. Its first equality is the zonotope norm as the polyhedral
norm (Kulmburg and Althoff's `Cor. 2`); the second, as printed, is
`maxᵢ ‖G'ᵀ λᵢ‖_{p*} / |bᵢ|` with `G' = [G, c - d]`, which is false
(`isGreatest_polyNorm_ellipsotope_counterexample`): a functional's sup over
`c + G B_p` is `‖Gᵀλ‖_{p*} + λᵀ(c - d)`, a sum, not the `p*`-norm of the pair. With that sum
it is exact, here for every `bᵢ > 0` and any norm on the coefficients:
`max(0, maxᵢ (‖λᵢ ∘ G‖ + λᵢ(c - d)) / bᵢ)`, which for a representation closed under
`λ ↦ -λ` is `maxᵢ (‖λᵢ ∘ G‖ + |λᵢ(c - d)|) / bᵢ`.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n s : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isGreatest_polyNorm_ellipsotope (G : E →ₗ[ℝ] Vec ℝ n) (c d : Vec ℝ n)
    {Λ : Mat ℝ s n} {b : Vec ℝ s} (hb : ∀ i, 0 < b i) :
    IsGreatest ((fun α => HPolytope.polyNorm Λ b (G α + c - d)) '' Metric.closedBall 0 1)
      ((insert 0 (Finset.univ.image fun i =>
        (‖LinearMap.toContinuousLinearMap ((HPolytope.rowLin Λ i).comp G)‖ + (Λ *ᵥ (c - d)) i)
          / b i)).max' (Finset.insert_nonempty _ _)) := by -- --- PROOF ---
  set f := fun i => LinearMap.toContinuousLinearMap ((HPolytope.rowLin Λ i).comp G) with hf
  set T := insert 0 (Finset.univ.image fun i => (‖f i‖ + (Λ *ᵥ (c - d)) i) / b i) with hT
  -- a row at `G α + c - d` is the functional at `α` plus the row at `c - d`
  have hrow : ∀ i α, (Λ *ᵥ (G α + c - d)) i = f i α + (Λ *ᵥ (c - d)) i := by
    intro i α
    rw [add_sub_assoc, mulVec_add, Pi.add_apply]
    rfl
  have hupper : ∀ α ∈ Metric.closedBall (0 : E) 1,
      HPolytope.polyNorm Λ b (G α + c - d) ≤ T.max' (Finset.insert_nonempty _ _) := by
    intro α hα
    refine HPolytope.polyNorm_le_iff.mpr ⟨T.le_max' 0 (Finset.mem_insert_self _ _), fun i => ?_⟩
    refine le_trans ?_ (T.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_univ i))))
    rw [hrow]
    refine div_le_div_of_nonneg_right ?_ (hb i).le
    have := (isGreatest_apply_closedBall (f i)).2 ⟨α, hα, rfl⟩
    linarith
  refine ⟨?_, fun _ ⟨α, hα, he⟩ => he ▸ hupper α hα⟩
  -- the largest term is attained: at `0`, or at a maximizer of its row
  rcases Finset.mem_insert.mp (T.max'_mem (Finset.insert_nonempty _ _)) with h0 | hi
  · refine ⟨0, Metric.mem_closedBall_self zero_le_one, le_antisymm (hupper 0
      (Metric.mem_closedBall_self zero_le_one)) ?_⟩
    rw [h0]
    exact (HPolytope.polyNorm_le_iff.mp le_rfl).1
  · obtain ⟨i, -, hie⟩ := Finset.mem_image.mp hi
    obtain ⟨⟨α, hα, hαe⟩, -⟩ := isGreatest_apply_closedBall (f i)
    refine ⟨α, hα, le_antisymm (hupper α hα) ?_⟩
    rw [← hie]
    refine le_trans ?_ ((HPolytope.polyNorm_le_iff.mp le_rfl).2 i)
    rw [hrow, hαe]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
