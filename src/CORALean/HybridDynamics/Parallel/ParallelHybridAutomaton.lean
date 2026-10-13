import CORALean.HybridDynamics.HybridAutomaton

/-!
# Parallel hybrid automata: the automaton and its runs

CORA's `parallelHybridAutomaton`: `k` component automata, each a `HybridAutomaton`
of its own dimension `n i`, and `binds`, CORA's `bindsInputs`: every input of a
component is either one of `m` global inputs or a state of some component.

The input is `u` in `ẋ = A x + u`, as `Location.Trajectory` has it: one input per state
coordinate, `binds i j` feeding coordinate `j` of component `i`. Where CORA binds an *output*
this binds a state, CORA's `C = I`, since `OutputEq` is kept off the system classes (#40).

`stack` puts the components' states side by side, through `finSigmaFinEquiv`; `globalInput`
zeroes the state-bound input coordinates, which the product keeps in its matrix.

`Run` is the semantics, and the product never enters it. A `Stay` is the shared time axis:
one dwell time `τ`, every component flowing in its location's invariant, inputs as bound; the
input set constrains only the global inputs, as in CORA. A `jump` ends a stay with one
component taking a transition; simultaneous jumps are consecutive, a zero-length stay between.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- ========================================  MAIN TYPE  ========================================= --

inductive InputSource (k : ℕ) (n : Fin k → ℕ) (m : ℕ) : Type where
  | global (a : Fin m) : InputSource k n m
  | state (c : Fin k) (s : Fin (n c)) : InputSource k n m

structure ParallelHybridAutomaton (S G : ℕ → Type) (k : ℕ) (L : Fin k → Type) (𝕋 : Type)
    (n : Fin k → ℕ) (m : ℕ) where
  comp : ∀ i, HybridAutomaton S G (L i) 𝕋 (n i)
  binds : ∀ i, Fin (n i) → InputSource k n m

-- The components' states side by side: coordinate `⟨i, j⟩` is coordinate `j` of component `i`.
def stack (x : ∀ i, Vec ℝ (n i)) : Vec ℝ (∑ i, n i) :=
  fun p => x (finSigmaFinEquiv.symm p).1 (finSigmaFinEquiv.symm p).2

-- The inputs a product keeps as its own: the globally bound coordinates, the rest zeroed.
def globalInput (binds : ∀ i, Fin (n i) → InputSource k n m) (v : ∀ i, Vec ℝ (n i)) :
    ∀ i, Vec ℝ (n i) :=
  fun i j => match binds i j with
    | .global _ => v i j
    | .state _ _ => 0

-- One shared dwell time; the input set constrains only the global inputs, as CORA's `bindsInputs`.
structure ParallelHybridAutomaton.Stay [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (ℓ : ∀ i, L i) (τ : ℝ) (x u : ∀ i, ℝ → Vec ℝ (n i)) (g : ℝ → Vec ℝ m) : Prop where
  nonneg : 0 ≤ τ
  input (i : Fin k) (t : ℝ) (ht : t ∈ Set.Icc 0 τ) :
    globalInput P.binds (fun i => u i t) i ∈ construct ((P.comp i).loc (ℓ i)).U
  flow (i : Fin k) (t : ℝ) (ht : t ∈ Set.Icc 0 τ) :
    HasDerivWithinAt (x i) (toRealMat ((P.comp i).loc (ℓ i)).dynamics.A *ᵥ x i t + u i t)
      (Set.Icc 0 τ) t
  invariant (i : Fin k) (t : ℝ) (ht : t ∈ Set.Icc 0 τ) :
    x i t ∈ construct ((P.comp i).loc (ℓ i)).inv
  bound (i : Fin k) (j : Fin (n i)) (t : ℝ) (ht : t ∈ Set.Icc 0 τ) :
    -- the binding decides: a global input at `t`, or a component's state at `t`
    u i t j = match P.binds i j with
      | .global a => g t a
      | .state c s => x c t s

inductive ParallelHybridAutomaton.Run [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] (P : ParallelHybridAutomaton S G k L 𝕋 n m) :
    (∀ i, L i) → (∀ i, Vec ℝ (n i)) → (∀ i, L i) → (∀ i, Vec ℝ (n i)) → Prop where
  | flow {ℓ : ∀ i, L i} {τ : ℝ} {x u : ∀ i, ℝ → Vec ℝ (n i)} {g : ℝ → Vec ℝ m}
      (h : P.Stay ℓ τ x u g) : P.Run ℓ (fun i => x i 0) ℓ (fun i => x i τ)
  -- one component `c` takes a transition at the end of the stay, the others stand still
  | jump {ℓ ℓ' : ∀ i, L i} {τ : ℝ} {x u : ∀ i, ℝ → Vec ℝ (n i)} {g : ℝ → Vec ℝ m}
      {y : ∀ i, Vec ℝ (n i)} {c : Fin k} {e : Transition G (L c) 𝕋 (n c)}
      (h : P.Stay ℓ τ x u g) (hmem : e ∈ ((P.comp c).loc (ℓ c)).trans)
      (hguard : x c τ ∈ construct e.guard)
      (rest : P.Run (Function.update ℓ c e.target)
        (Function.update (fun i => x i τ) c (e.reset (x c τ))) ℓ' y) :
      P.Run ℓ (fun i => x i 0) ℓ' y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
