module

public import CORALean.Global.KaucherInner

@[expose] public section

/-!
# Forward inner and outer reachable sets, the loop of Algorithm 1

[1, Alg. 1] steps through a time grid `t₀ < t₁ < … < t_N` carrying three enclosures: `[z_j]`
of the solutions from the initial box at `t_j`, `[z̃_j]` of the solution from the one point
`z̃₀`, and `[J_j]` of the Jacobian of the flow with respect to `z₀`. Per step: (Step 1) a priori
enclosures by the interval Picard-Lindelöf iteration, (Step 2) the Taylor models (15)-(17) of
the three on `[t_j, t_{j+1}]`, (Step 3) the inner range (18) for every `t` of the step, and
(Step 4) the Taylor models at `t_{j+1}` as the next enclosures.

Steps 1 and 2 are one argument here, `models`: the Taylor models of Sections 3.2 and 3.3 at time
`t`, from the enclosures at `t_j`. The validated Taylor-model integration they stand for is
not in this tree, nor is the differentiability of a flow with respect to its initial
condition, so what the loop needs of them is the hypothesis of the soundness theorem: from
valid enclosures at `t_j` they give valid enclosures at every `t` of the step. Step 3 is
[`kaucherInnerStep`](KaucherInner.lean), per component.

## References

* [1] E. Goubault and S. Putot. "Forward Inner-Approximated Reachability of Non-Linear
      Continuous Systems". In Proc. of the 20th International Conference on Hybrid Systems:
      Computation and Control (HSCC), pp. 1-10, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Matrix

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- What [1, Alg. 1] carries between steps: `[z_j]`, `[z̃_j]` and `[J_j]`, as bounds. -/
structure ForwardInnerState (n : ℕ) where
  zlo : Fin n → ℝ
  zhi : Fin n → ℝ
  ztlo : Fin n → ℝ
  zthi : Fin n → ℝ
  Jlo : Mat ℝ n n
  Jhi : Mat ℝ n n

/-- [1, Alg. 1]'s initialization `j = 0`, `[z₀] = z₀`, `[z̃₀] = z̃₀`, `[J₀] = Id`. -/
def forwardInnerInit (lo hi z₀ : Fin n → ℝ) : ForwardInnerState n where
  -- 0. Init: `[z₀] = z₀`, the initial box
  zlo := lo
  zhi := hi
  -- 0. Init: `[z̃₀] = z̃₀`, the one point
  ztlo := z₀
  zthi := z₀
  -- 0. Init: `[J₀] = Id`
  Jlo := 1
  Jhi := 1

/-- [1, Alg. 1]'s loop: the state at the grid time `t_j`, Steps 1-2 giving `models`, and
Step 4 taking their value at `t_{j+1}`. -/
def forwardInnerState (models : ℕ → ForwardInnerState n → ℝ → ForwardInnerState n)
    (t : ℕ → ℝ) (lo hi z₀ : Fin n → ℝ) : ℕ → ForwardInnerState n
  | 0 => forwardInnerInit lo hi z₀
  | j + 1 =>
    -- 4. `[z_j], [z̃_j], [J_j]`, the enclosures Step 4 of the passes before left at `t_j`
    let Z_j := forwardInnerState models t lo hi z₀ j
    -- 2. Steps 1-2 of the pass: the Taylor models (15)-(17) of `[t_j, t_{j+1}]`, read at `t_{j+1}`
    let Z_j1 := models j Z_j (t (j + 1))
    -- 4. Step 4: `[z_{j+1}], [z̃_{j+1}], [J_{j+1}]` are those models at `t_{j+1}`
    Z_j1

/-- [1, Alg. 1, Step 3] at time `t` of step `j`, component `i`: the (possibly improper) interval
`]z[ᵢ(t, t_j)` of (18), from the Taylor models (Steps 1-2) at `t`. -/
noncomputable def forwardInnerRange (models : ℕ → ForwardInnerState n → ℝ → ForwardInnerState n)
    (t : ℕ → ℝ) (lo hi z₀ : Fin n → ℝ) (j : ℕ) (τ : ℝ) (i : Fin n) : ℝ × ℝ :=
  -- 4. `[z_j], [z̃_j], [J_j]`, the enclosures Step 4 of the passes before left at `t_j`
  let Z_j := forwardInnerState models t lo hi z₀ j
  -- 2. Steps 1-2: the Taylor models (15)-(17) of `[t_j, t_{j+1}]`, read at `τ`
  let Z_τ := models j Z_j τ
  -- 3. Step 3: `]z[ᵢ(τ, t_j) = [z̃ᵢ](τ, …) + [Jᵢ](τ, …) ∗ ([z₀, z₀] − z̃₀)`, (18)
  kaucherInnerStep Z_τ.ztlo Z_τ.zthi Z_τ.Jlo Z_τ.Jhi lo hi z₀ i

/-- What the Taylor models must be: at time `τ`, `[z]` holds the flow of every initial value
of the box, `[z̃]` that of `z̃₀`, and `[J]` the Jacobian of the flow on the box. -/
def ForwardInnerState.Encloses (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (lo hi z₀ : Fin n → ℝ)
    (τ : ℝ) (s : ForwardInnerState n) : Prop :=
  (∀ z ∈ Icc lo hi, Φ τ z ∈ Icc s.zlo s.zhi) ∧ Φ τ z₀ ∈ Icc s.ztlo s.zthi ∧
    ∀ i j, ∀ y ∈ Icc lo hi,
      fderiv ℝ (fun z => Φ τ z i) y (Pi.single j 1) ∈ Icc (s.Jlo i j) (s.Jhi i j)


/-- Soundness of [1, Alg. 1] relative to its Taylor models: the carried enclosures are valid at
every grid time, and for every `t` of a step, the proper counterpart of each `]z[ᵢ` of Step 3 is
in the `i`-th projection of the reachable set at `t` (per component, not as a box). -/
theorem forwardInner_sound {Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)}
    {models : ℕ → ForwardInnerState n → ℝ → ForwardInnerState n} {t : ℕ → ℝ}
    {lo hi z₀ : Fin n → ℝ} (hz₀ : z₀ ∈ Icc lo hi)
    (hΦ : ∀ τ i, Differentiable ℝ fun z => Φ τ z i)
    (ht : Monotone t) (hΦ0 : ∀ z, Φ (t 0) z = z)
    (hmodels : ∀ j s, s.Encloses Φ lo hi z₀ (t j) → ∀ τ ∈ Icc (t j) (t (j + 1)),
      (models j s τ).Encloses Φ lo hi z₀ τ) : -- --- CONCL ---
    (∀ j, (forwardInnerState models t lo hi z₀ j).Encloses Φ lo hi z₀ (t j)) ∧
      ∀ j, ∀ τ ∈ Icc (t j) (t (j + 1)), ∀ i,
        Icc (forwardInnerRange models t lo hi z₀ j τ i).2
            (forwardInnerRange models t lo hi z₀ j τ i).1
          ⊆ (fun z => Φ τ z i) '' Icc lo hi := by -- --- PROOF ---
  -- at `t₀` the flow is the identity, with Jacobian `Id`
  have h0 : (forwardInnerInit lo hi z₀).Encloses Φ lo hi z₀ (t 0) := by
    have hid : Φ (t 0) = id := funext hΦ0
    refine ⟨fun z hz => ?_, ?_, fun i j y _ => ?_⟩
    · simpa [hid, forwardInnerInit] using hz
    · simp [hid, forwardInnerInit]
    · have : (fun z : Fin n → ℝ => Φ (t 0) z i) = fun z => z i := by simp [hid]
      rw [this]
      have hd : fderiv ℝ (fun z : Fin n → ℝ => z i) y = ContinuousLinearMap.proj i :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).fderiv
      rw [hd]
      simp [forwardInnerInit, Matrix.one_apply, Pi.single_apply]
  -- the loop keeps the enclosures valid, by induction over the grid
  have hinv : ∀ j, (forwardInnerState models t lo hi z₀ j).Encloses Φ lo hi z₀ (t j) := by
    intro j
    induction j with
    | zero => exact h0
    | succ j ih =>
      exact hmodels j _ ih (t (j + 1)) ⟨ht (Nat.le_succ j), le_rfl⟩
  -- Step 3 at `τ`: (18) from the valid models, per component
  refine ⟨hinv, fun j τ hτ i => ?_⟩
  have hm := hmodels j _ (hinv j) τ hτ
  exact kaucherInnerStep_inner i (hΦ τ i) hz₀ (by
    have := hm.2.1
    exact ⟨this.1 i, this.2 i⟩) (fun j' y hy => hm.2.2 i j' y hy)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
