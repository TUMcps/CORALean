module

public import CORALean.HybridDynamics.HybridAutomaton
public import CORALean.HybridDynamics.Definitions.ResolveSource

@[expose] public section

/-!
# Parallel hybrid automata: the automaton and its runs

CORA's `parallelHybridAutomaton`: `k` component automata, each a `HybridAutomaton` of its own
dimension `n i`, and `binds`, CORA's `bindsInputs`: input `j` of component `i` is global input `a`
or output `s` of component `c`. Every location of component `i` has `p i` inputs and `q i` outputs
(`inputs_eq`, `outputs_eq`); `bindsAt ℓ` is `binds` read at the locations `ℓ`, and `boundInput`
the value it gives an input. `IsRun` is the semantics, and the product never enters it. An `IsStay`
is the shared time axis: one dwell time `τ`, every component a Carathéodory run of its own equation
in its invariant, its disturbances in its `W`; the input set constrains only the global inputs. A
`jump` ends a stay with one component taking a transition; simultaneous jumps are consecutive.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- A parallel hybrid automaton: `k` component automata, and for each input of each component
whether it is a global input or the output of another component. -/
structure ParallelHybridAutomaton (S G : ℕ → Type) (k : ℕ) (L : Fin k → Type) (𝕋 : Type)
    (n : Fin k → ℕ) (m : ℕ) where
  comp : ∀ i, HybridAutomaton S G (L i) 𝕋 (n i)
  p : Fin k → ℕ
  q : Fin k → ℕ
  binds : ∀ i, Fin (p i) → ResolveSource k q m
  inputs_eq : ∀ i ℓ, ((comp i).loc ℓ).dynamics.m = p i
  outputs_eq : ∀ i ℓ, ((comp i).loc ℓ).dynamics.q = q i

/-- The flow of component `i` at the location tuple `ℓ`. -/
abbrev ParallelHybridAutomaton.sys (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (ℓ : ∀ i, L i) (i : Fin k) : LinearSys 𝕋 (n i) :=
  ((P.comp i).loc (ℓ i)).dynamics

/-- `binds` at the input and output dimensions of the locations `ℓ`. -/
def ParallelHybridAutomaton.bindsAt (P : ParallelHybridAutomaton S G k L 𝕋 n m) (ℓ : ∀ i, L i)
    (i : Fin k) (j : Fin (P.sys ℓ i).m) : ResolveSource k (fun c => (P.sys ℓ c).q) m :=
  match P.binds i (Fin.cast (P.inputs_eq i (ℓ i)) j) with
  | .global a => .global a
  | .output c s => .output c (Fin.cast (P.outputs_eq c (ℓ c)).symm s)

/-- The value the binding gives input `j` of component `i`: the global input, or the feeding
component's output `C x + D u + k`, noise-free. -/
def ParallelHybridAutomaton.boundInput (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (ℓ : ∀ i, L i) (x : ∀ i, Vec ℝ (n i)) (u : ∀ i, Vec ℝ (P.sys ℓ i).m) (g : Vec ℝ m)
    (i : Fin k) (j : Fin (P.sys ℓ i).m) : ℝ :=
  match P.bindsAt ℓ i j with
  | .global a => g a
  | .output c s => (toRealMat (P.sys ℓ c).C *ᵥ x c + toRealMat (P.sys ℓ c).D *ᵥ u c +
      toRealVec (P.sys ℓ c).k) s

-- One shared dwell time; the input set constrains only the global inputs, as CORA's `bindsInputs`.
/-- A stay of all components over one dwell time: the global inputs lie in the input sets, each
component follows its location's linear dynamics inside its invariant, and its inputs are the bound
ones. -/
structure ParallelHybridAutomaton.IsStay [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (ℓ : ∀ i, L i) (τ : ℝ) (x : ∀ i, ℝ → Vec ℝ (n i)) (u : ∀ i, ℝ → Vec ℝ (P.sys ℓ i).m)
    (w : ∀ i, ℝ → Vec ℝ (P.sys ℓ i).r) (g : ℝ → Vec ℝ m) : Prop where
  nonneg : 0 ≤ τ
  input (i : Fin k) (t : ℝ) (ht : t ∈ Set.Icc 0 τ) :
    ∃ v ∈ construct ((P.comp i).loc (ℓ i)).U, ∀ j a, P.bindsAt ℓ i j = .global a → v j = g t a
  dist (i : Fin k) (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : w i t ∈ construct ((P.comp i).loc (ℓ i)).W
  -- every component a Carathéodory run of its own location's whole equation
  meas (i : Fin k) : AEStronglyMeasurable (fun s => toRealMat (P.sys ℓ i).A *ᵥ x i s +
    toRealMat (P.sys ℓ i).B *ᵥ u i s + toRealVec (P.sys ℓ i).c + toRealMat (P.sys ℓ i).E *ᵥ w i s)
      (volume.restrict (Set.Icc 0 τ))
  integrable (i : Fin k) (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : IntervalIntegrable (fun s =>
    toRealMat (P.sys ℓ i).A *ᵥ x i s + toRealMat (P.sys ℓ i).B *ᵥ u i s +
      toRealVec (P.sys ℓ i).c + toRealMat (P.sys ℓ i).E *ᵥ w i s) volume 0 t
  cont (i : Fin k) : ContinuousOn (x i) (Set.Icc 0 τ)
  flow (i : Fin k) (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : x i t = x i 0 + ∫ s in (0:ℝ)..t,
    (toRealMat (P.sys ℓ i).A *ᵥ x i s + toRealMat (P.sys ℓ i).B *ᵥ u i s +
      toRealVec (P.sys ℓ i).c + toRealMat (P.sys ℓ i).E *ᵥ w i s)
  invariant (i : Fin k) (t : ℝ) (ht : t ∈ Set.Icc 0 τ) :
    x i t ∈ construct ((P.comp i).loc (ℓ i)).inv
  bound (i : Fin k) (j : Fin (P.sys ℓ i).m) (t : ℝ) (ht : t ∈ Set.Icc 0 τ) :
    u i t j = P.boundInput ℓ (fun c => x c t) (fun c => u c t) (g t) i j

/-- The runs of a parallel automaton: a joint stay, or a stay after which one component takes a
transition while the others stand still. -/
inductive ParallelHybridAutomaton.IsRun [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] (P : ParallelHybridAutomaton S G k L 𝕋 n m) :
    (∀ i, L i) → (∀ i, Vec ℝ (n i)) → (∀ i, L i) → (∀ i, Vec ℝ (n i)) → Prop where
  | flow {ℓ : ∀ i, L i} {τ : ℝ} {x : ∀ i, ℝ → Vec ℝ (n i)} {u w} {g : ℝ → Vec ℝ m}
      (h : P.IsStay ℓ τ x u w g) : P.IsRun ℓ (fun i => x i 0) ℓ (fun i => x i τ)
  -- one component `c` takes a transition at the end of the stay, the others stand still
  | jump {ℓ ℓ' : ∀ i, L i} {τ : ℝ} {x : ∀ i, ℝ → Vec ℝ (n i)} {u w} {g : ℝ → Vec ℝ m}
      {y : ∀ i, Vec ℝ (n i)} {c : Fin k} {e : Transition G (L c) 𝕋 (n c)}
      (h : P.IsStay ℓ τ x u w g) (hmem : e ∈ ((P.comp c).loc (ℓ c)).trans)
      (hguard : x c τ ∈ construct e.guard)
      (rest : P.IsRun (Function.update ℓ c e.target)
        (Function.update (fun i => x i τ) c (e.reset (x c τ))) ℓ' y) :
      P.IsRun ℓ (fun i => x i 0) ℓ' y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
