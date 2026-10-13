module

public import CORALean.ContSet.Interval.Real.Theorems.EnclosePointsOuter
public import CORALean.ContSet.Zonotope.Real.Operations.Cloud2zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.Cloud2zonotopeCompressMem
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# `Zonotope.cloud2zonotope` contains every point

[1, Alg. 3]: the zonotope returned contains the whole cloud, "guaranteed to contain all the
point-vectors". Invariant of the loop: each original point minus its current residual lies in the
zonotope built so far. A round recentres the residual by `mid`, which `c := c + mid` takes up,
and compressing moves it by `t g` with `|t| ≤ 1` (`cloud2zonotopeCompress_mem`), which the segment
`⟨mid, g⟩` takes up. The residual left at the end lies in its interval hull, a zonotope.

Outer only, and for every `dir`, `ratio`, `s₁` and `s₂`: the choice of principal direction and
of ratio decides how tight the zonotope is, never whether it encloses.

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ} {κ : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cloud2zonotope_mem [Fintype κ] [Nonempty κ] (dir : (κ → Vec ℝ n) → Vec ℝ n)
    (ratio : ℝ) (s₁ : ℕ) (s₂ : ℝ) (X : κ → Vec ℝ n) (j : κ) :
    X j ∈ (Zonotope.cloud2zonotope dir ratio s₁ s₂ X).construct := by -- --- PROOF ---
  -- one round: recentre by `mid`, compress along `g`, add the segment `⟨mid, g⟩`
  have step : ∀ (Z : Zonotope (Vec ℝ n)) (Y : κ → Vec ℝ n) (mid g : Vec ℝ n),
      (∀ j, X j - Y j ∈ Z.construct) →
      ∀ j, X j - Zonotope.cloud2zonotopeCompress (fun j => Y j - mid) g j ∈
        (Z.plus ⟨1, mid, fun _ => g⟩).construct := by
    intro Z Y mid g h j
    rw [← Zonotope.plus_exact]
    obtain ⟨t, ht, hY⟩ := Zonotope.cloud2zonotopeCompress_mem (fun j => Y j - mid) g j
    refine ⟨X j - Y j, h j, mid + t • g, ⟨fun _ => t, fun _ => ht, by simp⟩, ?_⟩
    have : Y j - mid = Zonotope.cloud2zonotopeCompress (fun j => Y j - mid) g j + t • g := hY
    rw [eq_sub_of_add_eq' this.symm]
    abel_nf
  -- the loop keeps `X j - Y j ∈ Z`
  have key : ∀ (k iter : ℕ) (w : Vec ℝ n) (Z : Zonotope (Vec ℝ n)) (Y : κ → Vec ℝ n),
      (∀ j, X j - Y j ∈ Z.construct) →
      ∀ j, X j - (Zonotope.cloud2zonotopeLoop dir ratio s₂ k iter w Z Y).2 j ∈
        (Zonotope.cloud2zonotopeLoop dir ratio s₂ k iter w Z Y).1.construct := by
    intro k
    induction k with
    | zero => intro iter w Z Y h; simpa [Zonotope.cloud2zonotopeLoop] using h
    | succ k ih =>
      intro iter w Z Y h
      simp only [Zonotope.cloud2zonotopeLoop]
      split_ifs <;> first
        | exact ih _ _ _ _ (step Z Y _ _ h)
        | exact step Z Y _ _ h
  -- start with the empty zonotope `⟨0, 0⟩`, then box the residual
  have h0 : ∀ j, X j - X j ∈ (⟨0, 0, Fin.elim0⟩ : Zonotope (Vec ℝ n)).construct :=
    fun j => ⟨Fin.elim0, fun i => i.elim0, by simp⟩
  set L := Zonotope.cloud2zonotopeLoop dir ratio s₂ s₁ 0 0 ⟨0, 0, Fin.elim0⟩ X with hL
  have hres := key s₁ 0 0 _ X h0 j
  have hbox := Interval.zonotope_contains _ (Interval.enclosePoints_outer L.2 j)
  unfold Zonotope.cloud2zonotope
  rw [← Zonotope.plus_exact]
  exact ⟨X j - L.2 j, hres, L.2 j, hbox, by abel_nf⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
