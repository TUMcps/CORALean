module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.EuclideanNorm
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Zonotope.normExactCora`, CORA's `norm(Z,2,'exact')`

`norm(Z,2,'exact')` (`@contSet/norm.m`, `@zonotope/norm_.m`: "computes maximum norm value") runs
`private/priv_norm_exact.m`. It solves `min_{b ∈ {0,1}ᵐ} 4 (b - ½)ᵀ M (b - ½)` with
`M = λ_max I - GᵀG` (l. 52-54; YALMIP at l. 126-132, MOSEK's equivalent cone program at l. 99-114
has the same minimisers), i.e. maximises `‖G u‖` over `u = 2b - 1 ∈ {-1, 1}ᵐ`, ignoring the
center, and then returns `‖G u* + c‖` (l. 124/133, 140). `binprog` is the solver, a caller's
argument; `lmax` too, since the minimisers do not depend on it. `G = []` (l. 44-47) gives `‖c‖`
either way. One `let` per line of the source.

# CORA's `norm(Z,2,'exact')` under-estimates the largest norm

For `Z = zonotope([2;-20],[1 1;0 1])`, `‖G u‖²` over `u ∈ {-1, 1}²` is `5` at `±(1, 1)` and `1`
otherwise, so every minimiser of CORA's binary program gives `x = (4, -19)` or `x = (0, -21)`,
`‖x‖ = √377` or `√441`. The point `(2, -21) = c + G (1, -1)` of `Z` has norm `√445`, the true
maximum: whatever solver and `λ` CORA uses, `Zonotope.normExactCora` is strictly below it.

## References

* [1] `contSet/@zonotope/private/priv_norm_exact.m`, CORA, ll. 43-54, 123-140.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- [1] at the solver `binprog`, which returns a point of `{0, 1}ᵐ` (as `Bool`s) for an
objective. -/
noncomputable def Zonotope.normExactCora (Z : Zonotope (Vec ℝ n)) (lmax : ℝ)
    (binprog : ((Fin Z.h → Bool) → ℝ) → (Fin Z.h → Bool)) : ℝ :=
  -- l. 43, 49-50: `G = Z.G`, `m`, `c = Z.c`
  let G := Z.G
  let m := Z.h
  let c := Z.c
  -- l. 52: `GG = G'*G`
  let GG : Mat ℝ m m := Matrix.of fun j k => G j ⬝ᵥ G k
  -- l. 54: `M = lmax*eye(m) - GG`
  let M : Mat ℝ m m := lmax • (1 : Mat ℝ m m) - GG
  -- l. 126-127: `b = binvar(m,1)`, `obj = 4*(b-0.5)'*M*(b-0.5)`
  let half : (Fin m → Bool) → Vec ℝ m := fun b j => (if b j then 1 else 0) - 1 / 2
  let obj : (Fin m → Bool) → ℝ := fun b => 4 * (half b ⬝ᵥ (M *ᵥ half b))
  -- l. 132: `optimize([], obj, options)`
  let b := binprog obj
  -- l. 133: `x = G*value(2*(b-0.5))+c`
  let x : Vec ℝ n := ∑ j, (2 * half b j) • G j + c
  -- l. 140: `val = norm(x)`
  ‖x‖₂

end CORALean.Real

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.normExactCora_lt :
    let Z : Zonotope (Vec ℝ 2) := ⟨2, ![(2 : ℝ), -20], ![![1, 0], ![1, 1]]⟩
    ![(2 : ℝ), -21] ∈ Z.construct ∧
      ∀ (lmax : ℝ) (binprog : ((Fin Z.h → Bool) → ℝ) → (Fin Z.h → Bool)),
        (∀ (f : (Fin Z.h → Bool) → ℝ) b, f (binprog f) ≤ f b) →
          Z.normExactCora lmax binprog < ‖![(2 : ℝ), -21]‖₂ := by -- --- PROOF ---
  intro Z
  -- `(2, -21) = c + G (1, -1)`; CORA's objective, as `normExactCora` unfolds it
  refine ⟨⟨![1, -1], fun j => ?_, ?_⟩, fun lmax binprog hopt => ?_⟩
  · fin_cases j <;> simp
  · funext i
    fin_cases i <;> simp [Z, Fin.sum_univ_two]
    norm_num
  · let half : (Fin 2 → Bool) → Vec ℝ 2 := fun b j => (if b j then 1 else 0) - 1 / 2
    let obj : (Fin 2 → Bool) → ℝ := fun b => 4 * (half b ⬝ᵥ
      ((lmax • (1 : Mat ℝ 2 2) - Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k) *ᵥ half b))
    have hle : ∀ b', obj (binprog obj) ≤ obj b' := hopt obj
    change ‖∑ j, (2 * half (binprog obj) j) • Z.G j + Z.c‖₂ < _
    generalize binprog obj = s at hle ⊢
    -- `obj = 2λ - ‖G u‖²`: `2λ - 5` at `±(1, 1)`, `2λ - 1` at the others, so `s` is constant
    have htt := hle fun _ => true
    have hff := hle fun _ => false
    rw [norm₂, norm₂]
    apply Real.sqrt_lt_sqrt (by positivity)
    cases h0 : s 0 <;> cases h1 : s 1 <;>
      simp [obj, half, Z, dotProduct, mulVec, Fin.sum_univ_two, h0, h1] at htt hff ⊢ <;>
      norm_num at htt hff ⊢
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
