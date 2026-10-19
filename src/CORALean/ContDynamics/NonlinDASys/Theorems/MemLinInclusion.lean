module

public import CORALean.ContDynamics.NonlinDASys.Definitions.LinInclusion
public import CORALean.ContDynamics.NonlinDASys.Theorems.AlgDeviationEq

@[expose] public section

/-!
# A consistent state's derivative lies in the abstracting inclusion

[1, Eq. 13] and [1, Eq. 16]: inserting the algebraic deviation ([1, Eq. 12]) into the
linearized dynamics ([1, Eq. 10]) gives `ẋ = w + Ã Δx + B̃ Δu + (ℓᵈ - C F⁻¹ ℓᵃ)`, so
`ẋ ∈ Ã Δx ⊕ Ũ` once `L` holds `ℓᵈ - C F⁻¹ ℓᵃ` and `u ∈ U`.

`ℓᵈ = f(z) - (f(z*) + A Δx + B Δu + C Δy)` and `ℓᵃ = g(z) - (g(z*) + D Δx + E Δu + F Δy)` are
the exact linearization errors at `z = (x, y, u)`, and the hypothesis is that `L` holds their
combination. [1, Eq. 15] prints `L` with one Lagrange point `ξ` for all rows of `f` and
`g`, which need not hold it (`SharedLagrangePoint`); with one `ξ` per row,
[1, Eq. 8], it does (`NonlinDASys.exists_lagrange_remainder`), and so does every enclosure
[1, Cor. 1] computes. The state must be consistent, `g(z) = 0`, and only `F⁻¹ F = I` is used.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix
open scoped Pointwise

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 13], [1, Eq. 16]: at a consistent `z = (x, y, u)`, `u ∈ U`, with `L` holding
`ℓᵈ - C F⁻¹ ℓᵃ`, `f(z) ∈ Ã (x - x*) ⊕ Ũ`. -/
theorem NonlinDASys.mem_linInclusion (sys : NonlinDASys n p m) {xs : Vec ℝ n} {ys : Vec ℝ p}
    {us : Vec ℝ m} {A : Mat ℝ n n} {B : Mat ℝ n m} {C : Mat ℝ n p} {D : Mat ℝ p n}
    {E : Mat ℝ p m} {F F_inv : Mat ℝ p p} (hF : F_inv * F = 1) {U : Set (Vec ℝ m)}
    {L : Set (Vec ℝ n)} {x : Vec ℝ n} {y : Vec ℝ p} {u : Vec ℝ m} (hu : u ∈ U)
    (hg : sys.g x y u = 0)
    (hL : (sys.f x y u - (sys.f xs ys us + A *ᵥ (x - xs) + B *ᵥ (u - us) + C *ᵥ (y - ys)))
      - (C * F_inv) *ᵥ (sys.g x y u - (sys.g xs ys us + D *ᵥ (x - xs) + E *ᵥ (u - us)
        + F *ᵥ (y - ys))) ∈ L) : -- --- CONCL ---
    sys.f x y u ∈ NonlinDASys.linInclusion (sys.f xs ys us) (sys.g xs ys us) A B C D E F_inv
      us U L (x - xs) := by -- --- PROOF ---
  set ℓd := sys.f x y u - (sys.f xs ys us + A *ᵥ (x - xs) + B *ᵥ (u - us) + C *ᵥ (y - ys))
    with hℓd
  set ℓa := sys.g x y u - (sys.g xs ys us + D *ᵥ (x - xs) + E *ᵥ (u - us) + F *ᵥ (y - ys))
    with hℓa
  -- [1, Eq. 12]: the algebraic deviation from the constraint
  have hΔy : y - ys = -(F_inv *ᵥ (sys.g xs ys us + D *ᵥ (x - xs) + E *ᵥ (u - us)))
      - F_inv *ᵥ ℓa :=
    NonlinDASys.alg_deviation_eq hF (by rw [hℓa, hg]; abel)
  refine ⟨(A - C * F_inv * D) *ᵥ (x - xs), rfl, _,
    ⟨_, ⟨sys.f xs ys us - (C * F_inv) *ᵥ sys.g xs ys us, rfl, _,
      ⟨u - us, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩, ℓd - (C * F_inv) *ᵥ ℓa, hL, rfl⟩, ?_⟩
  -- [1, Eq. 13]: `f(z) = f(z*) + A Δx + B Δu + C Δy + ℓᵈ` with `Δy` inserted
  have hf : sys.f x y u = sys.f xs ys us + A *ᵥ (x - xs) + B *ᵥ (u - us) + C *ᵥ (y - ys) + ℓd := by
    rw [hℓd]; abel
  rw [hf, hΔy]
  simp only [Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_neg,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
