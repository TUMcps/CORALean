import CORALean.Specification.STL.Operations.VerifySTLKochdumperGloballyCora
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith

/-!
# CORA's STL verifier returns `verified` for a violated `G_[0,1] ((-1 ≤ x ≤ 1) ∨ x ≥ 10)`

`linearSys/verify` with `options.verifyAlg = 'stl:kochdumper'` ([1]) on `ẋ = 0` (`A = 0`, `B = 0`,
`U = zonotope(0)`, as in CORA's `test_linearSys_verify_01_temporalLogic`), `R0 = zonotope(-1,1)
= [-2, 0]`, `tFinal = 1` and `globally((x(1) >= -1 & x(1) <= 1) | x(1) >= 10, interval(0,1))`.
The run `x ≡ -2` starts in `R0` and violates the formula at every time. The two clauses make
`sets{1}` a union of unsafe polytopes (`aux_safe2unsafe`, reversed rows shifted by `eps`):
`x ≤ -1 - eps ∧ x ≤ 10 - eps` and then `x ≥ 1 + eps ∧ x ≤ 10 - eps`. The reachable set `[-2, 0]`
meets the first (code `2`; the quick checks fail, `isIntersecting` is true) but `any(c - rad > d)`
holds for the second (`0 > -1 - eps`), so `res = max(list(i))` (l. 955) is `1` on every time
interval and point; `evalPredicates` turns `globally(φ,[0,2])` into `stl(true)` and
`aux_modelCheckReachSet` returns `res = true` (l. 221): CORA reports the specification verified.
`isIntersecting` is any test returning `true` on sets that meet (CORA's exact test does); `ε` is
any shift in `[0, 1)`, CORA's `eps` among them; real arithmetic, every comparison by margin `≥ 1`.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.verifySTLKochdumperGloballyCora_unionLastOnly_counterexample
    (isIntersecting : Set (Fin 1 → ℝ) → Set (Fin 1 → ℝ) → Bool)
    (hsound : ∀ S T, (S ∩ T).Nonempty → isIntersecting S T = true)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) :
    let c₀ : Fin 1 → ℝ := fun _ => -1                          -- R0 = zonotope(-1,1)
    let G₀ : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    let S₁ : List ((Fin 1 → ℝ) × ℝ) := [(fun _ => -1, 1), (fun _ => 1, 1)]  -- x >= -1 & x <= 1
    let S₂ : List ((Fin 1 → ℝ) × ℝ) := [(fun _ => -1, -10)]                 -- x >= 10
    let φ : ℝ → Prop := fun x => (x ≥ -1 ∧ x ≤ 1) ∨ x ≥ 10
    -- `convert2set`'s clauses are `φ`
    (∀ x : Fin 1 → ℝ, φ (x 0) ↔ ∃ S ∈ [S₁, S₂], ∀ r ∈ S, ∑ j, r.1 j * x j ≤ r.2) ∧
    -- a run of `ẋ = 0` from `R0` violates `G_[0,1] φ`
    (∃ x : ℝ → ℝ, (∃ a ∈ Set.Icc (-1 : ℝ) 1, x 0 = c₀ 0 + G₀ 0 0 * a) ∧
      (∀ t, HasDerivAt x 0 t) ∧ ∃ t ∈ Set.Icc (0 : ℝ) 1, ¬ φ (x t)) ∧
    -- CORA returns `res = true`: verified
    STL.verifySTLKochdumperGloballyCora isIntersecting ε c₀ G₀ 1 [S₁, S₂] =
      some true := by -- --- PROOF ---
  intro c₀ G₀ S₁ S₂ φ
  refine ⟨?_, ⟨fun _ => -2, ⟨-1, by norm_num, by simp [c₀, G₀]; norm_num⟩,
    fun t => hasDerivAt_const t _, 0, by norm_num, by simp [φ]; norm_num⟩, ?_⟩
  · intro x
    simp only [φ, S₁, S₂, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, forall_eq_or_imp, forall_eq, Fin.sum_univ_one]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · left; constructor <;> linarith
      · right; linarith
    · rintro (⟨h1, h2⟩ | h)
      · left; constructor <;> linarith
      · right; linarith
  · -- `aux_safe2unsafe`: both pairs meet, so both intersections are kept
    simp only [STL.verifySTLKochdumperGloballyCora, STL.safeToUnsafeCora, S₁, S₂, List.foldl,
      List.map, List.flatMap, List.filterMap]
    rw [if_pos (hsound _ _ ?h1), if_pos (hsound _ _ ?h2)]
    case h1 => exact ⟨fun _ => -2, by simp; linarith, by simp; linarith⟩
    case h2 => exact ⟨fun _ => 2, by simp; linarith, by simp; linarith⟩
    simp only [List.nil_append, List.cons_append]
    -- `R0` meets the first unsafe set (code `2`), the second is disjoint (code `1`)
    have hE : STL.evaluatePredicateUnionPolytopeCora isIntersecting c₀ G₀ Finset.univ
        [[(-fun _ => -1, -1 - ε), (-fun _ => -1, - -10 - ε)],
          [(-fun _ => 1, -1 - ε), (-fun _ => -1, - -10 - ε)]] = 1 := by
      have hI : isIntersecting {x | ∃ a : Fin 1 → ℝ, (-1 ≤ a 0 ∧ a 0 ≤ 1) ∧ x = fun _ => -1 + a 0}
          {x | x 0 ≤ -1 - ε ∧ x 0 ≤ 10 - ε} = true :=
        hsound _ _ ⟨fun _ => -2, ⟨fun _ => -1, by norm_num, by funext; norm_num⟩, by
          simp only [Set.mem_setOf_eq]; constructor <;> linarith⟩
      have h1 : ¬ (1 < ε ∨ 10 - ε < -1 - 1) := by
        rintro (h | h) <;> linarith
      have h2 : ¬ (ε ≤ -1 ∧ ε ≤ 10) := by
        rintro ⟨h, -⟩; linarith
      have h3 : -1 < ε ∨ 10 - ε < -1 - 1 := Or.inl (by linarith)
      simp [STL.evaluatePredicateUnionPolytopeCora, c₀, G₀, hI, h1, h2, h3]
    -- every code is `1`, so `evalPredicates` gives `stl(true)`
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hE]
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
