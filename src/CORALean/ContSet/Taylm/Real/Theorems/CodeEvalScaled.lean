module

public import CORALean.ContSet.Taylm.Real.Operations.CodeEval
public import CORALean.ContSet.Taylm.Real.Definitions.CodeScale
public import CORALean.ContSet.Taylm.Real.Theorems.PlusScaled
public import CORALean.ContSet.Taylm.Real.Theorems.TimesScaled
public import CORALean.ContSet.Taylm.Real.Theorems.UminusScaled
public import CORALean.ContSet.Taylm.Real.Theorems.ExpScaled
public import CORALean.ContSet.Taylm.Real.Theorems.SinScaled
public import CORALean.ContSet.Taylm.Real.Theorems.CosScaled
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorMaxOrder

@[expose] public section

/-!
# A code list keeps the `(n+1)`-st order scaling

[1, Thm. 2]'s second claim: "if the Taylor model of `f` has the `(n+1)`-st order scaling property,
so does the resulting Taylor model for `g`". By induction over the code list from [1, Thm. 1]'s
lemmas: inputs scaled by `C` at order `N` give a result scaled by `codeScale N e C`, a constant
that does not depend on `h`. Shown for `ScalingFragment`, the code lists whose intrinsics are
`exp`, `sin` and `cos`; the others need a uniform bound on their derivative bound away from
the edge of their domain, which `taylor_scaled` takes as a hypothesis.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A constant is scaled by its magnitude. -/
theorem Taylm.aux_const_scaled (c : ℝ) (N : ℕ) {h : ℝ} (h0 : 0 < h) :
    (Taylm.const n c N).Scaled h |c| := by -- --- PROOF ---
  have hp : 0 ≤ |c| * h ^ (N + 1) := mul_nonneg (abs_nonneg _) (pow_pos h0 _).le
  refine ⟨?_, ?_, ?_⟩
  · simp [Taylm.const, Taylm.weight, Taylm.degree]
  · simpa [Taylm.const] using hp
  · simpa [Taylm.const] using hp


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.codeEval_scaled {m : ℕ} {N : ℕ} {F : Fin m → Taylm n} {h C : ℝ} (h0 : 0 < h)
    (h1 : h ≤ 1) (hN : ∀ i, (F i).maxOrder = N) (hF : ∀ i, (F i).Scaled h C) : -- --- STMT ---
    ∀ (e : Taylm.CodeList ℝ m), e.ScalingFragment → ∀ {T : Taylm n},
      Taylm.codeEval N F e = some T →
        T.maxOrder = N ∧ T.Scaled h (Taylm.codeScale N C e) := by -- --- PROOF ---
  intro e
  induction e with
  -- an input or a constant
  | var i =>
    intro _ T hT
    simp only [Taylm.codeEval, Option.some.injEq] at hT
    exact hT ▸ ⟨hN i, hF i⟩
  | const c =>
    intro _ T hT
    simp only [Taylm.codeEval, Option.some.injEq] at hT
    exact hT ▸ ⟨rfl, Taylm.aux_const_scaled c N h0⟩
  -- the two binary operations, at the order both operands keep
  | add a b iha ihb =>
    intro hfr T hT
    simp only [Taylm.codeEval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hT
    obtain ⟨A, hA, B, hB, rfl⟩ := hT
    obtain ⟨oA, sA⟩ := iha hfr.1 hA
    obtain ⟨oB, sB⟩ := ihb hfr.2 hB
    exact ⟨by simp [Taylm.plus, oA, oB], Taylm.plus_scaled (oA.trans oB.symm) sA sB⟩
  | mul a b iha ihb =>
    intro hfr T hT
    simp only [Taylm.codeEval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hT
    obtain ⟨A, hA, B, hB, rfl⟩ := hT
    obtain ⟨oA, sA⟩ := iha hfr.1 hA
    obtain ⟨oB, sB⟩ := ihb hfr.2 hB
    exact ⟨by simp [Taylm.times, oA, oB], Taylm.times_scaled h0 h1 (oA.trans oB.symm) sA sB⟩
  -- negation keeps everything; an intrinsic is one of the three
  | neg a iha =>
    intro hfr T hT
    simp only [Taylm.codeEval, Option.map_eq_some_iff] at hT
    obtain ⟨A, hA, rfl⟩ := hT
    obtain ⟨oA, sA⟩ := iha hfr hA
    exact ⟨by simp [Taylm.uminus, oA], Taylm.uminus_scaled sA⟩
  | intr s a iha =>
    intro hfr T hT
    simp only [Taylm.codeEval, Option.bind_eq_some_iff] at hT
    obtain ⟨A, hA, hs⟩ := hT
    obtain ⟨oA, sA⟩ := iha hfr.2 hA
    rcases hfr.1 with rfl | rfl | rfl <;>
      simp only [Taylm.intrinsic, Option.some.injEq] at hs <;> subst hs
    -- each keeps the order, and its `_scaled` theorem gives the constant
    · refine ⟨by simp [Taylm.exp, Taylm.taylor_maxOrder, oA], ?_⟩
      have := Taylm.exp_scaled h0 h1 sA
      rwa [oA] at this
    · refine ⟨by simp [Taylm.sin, Taylm.taylor_maxOrder, oA], ?_⟩
      have := Taylm.sin_scaled h0 h1 sA
      rwa [oA] at this
    · refine ⟨by simp [Taylm.cos, Taylm.taylor_maxOrder, oA], ?_⟩
      have := Taylm.cos_scaled h0 h1 sA
      rwa [oA] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
