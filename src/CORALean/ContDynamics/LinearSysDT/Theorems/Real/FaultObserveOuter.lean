module

public import CORALean.ContSet.Zonotope.Real.Operations.FaultObserve
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The fault-detection observer encloses the fault-free state

[1, Eq. 10]: if `x_k` lies in `X̂_k`, here already reduced by `↓_q` (an outer reduction keeps
`x_k` in it), then `x_{k+1} = A x_k + B u_k + D_x w_k` lies in `⟨p_{k+1}, H_{k+1}⟩`
(`Zonotope.faultObserve`) for every gain `L`, `w_k = H_w s₁`, `v_k = H_v s₂` with `s₁`, `s₂` in
the unit boxes [1, Eq. 4], [1, Eq. 5], **provided `f_k = 0`**: the output `y_k = C x_k + D_y v_k`
the observer reads carries no fault. [1, Eq. 10] states it for the system [1, Eq. 3] with its
sensor fault `E f_k`, which the zonotope does not account for; a fault moves `y_k` and with it
the center, which is what the test [1, Eq. 31] detects. A point of `X̂_k` is `p_k + θ`, and
`x_{k+1} = p_{k+1} + (A - LC) θ + D_x H_w s₁ - L D_y H_v s₂`.

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n nu ny nw nv rw rv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.faultObserve_outer (A : Mat ℝ n n) (B : Mat ℝ n nu) (C : Mat ℝ ny n)
    (L : Mat ℝ n ny) (Dx : Mat ℝ n nw) (Hw : Mat ℝ nw rw) (Dy : Mat ℝ ny nv) (Hv : Mat ℝ nv rv)
    (u : Vec ℝ nu) (X : Zonotope (Vec ℝ n)) (x : Vec ℝ n) (s₁ : Vec ℝ rw) (s₂ : Vec ℝ rv)
    (hx : x ∈ X.construct) (hs₁ : ∀ i, |s₁ i| ≤ 1) (hs₂ : ∀ i, |s₂ i| ≤ 1) :
    A *ᵥ x + B *ᵥ u + Dx *ᵥ (Hw *ᵥ s₁) ∈ (X.faultObserve A B C L Dx Hw Dy Hv u
      (C *ᵥ x + Dy *ᵥ (Hv *ᵥ s₂))).construct := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hx
  -- a matrix's columns weighted by a vector are the matrix times it
  have hcol : ∀ {k : ℕ} (G : Mat ℝ n k) (v : Vec ℝ k), ∑ j, v j • (fun i => G i j) = G *ᵥ v :=
    fun G v => by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  have hcolneg : ∀ {k : ℕ} (G : Mat ℝ n k) (v : Vec ℝ k),
      ∑ j, v j • (fun i => -G i j) = -(G *ᵥ v) := fun G v => by
    ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  set θ : Vec ℝ n := ∑ j, β j • X.G j
  refine ⟨Fin.append (Fin.append β s₁) s₂, ?_, ?_⟩
  · -- every coefficient is in `[-1, 1]`
    intro j
    refine Fin.addCases (fun j => Fin.addCases (fun j => ?_) (fun j => ?_) j) (fun j => ?_) j <;>
      simp [hβ, hs₁, hs₂]
  · -- the three generator blocks summed
    show _ = _ + ∑ j : Fin (X.h + rw + rv), _
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Zonotope.faultObserve, Fin.append_left, Fin.append_right]
    have hX : ∑ j, β j • ((A - L * C) *ᵥ X.G j) = (A - L * C) *ᵥ θ := by
      simp only [θ, mulVec_sum, mulVec_smul]
    rw [hX, hcol, hcolneg]
    simp only [sub_mulVec, ← mulVec_mulVec, mulVec_add, mulVec_sub]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
