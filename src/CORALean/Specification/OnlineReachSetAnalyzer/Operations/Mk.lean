module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Parse
public import CORALean.Specification.OnlineReachSetAnalyzer.OnlineReachSetAnalyzer

@[expose] public section

/-!
# The constructor

`analyzer = onlineReachSetAnalyzer(phi,propagationFrequency,dropPropagated)`: the formula, after
`desugar`, is parsed into the syntax DAG, nothing is propagated yet, and the leaves are the nodes
that are nobody's parent, `setdiff(1:length(obj.nodes),vertcat(obj.nodes.parents))`.
`propagationFrequency` defaults to `1`, `dropPropagated` to `true` (turned off only for debugging
and visualization).

## Inputs
* `φ` – formula to monitor
* `propagationFrequency` – observations between propagations
* `dropPropagated` – drop propagated times flag

## Output
* the analyzer, or none if parsing fails
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] [Float.ExactLe 𝕋]
  [TimeOrder 𝕋]
    {S : ℕ → Type} {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `analyzer = onlineReachSetAnalyzer(phi,propagationFrequency,dropPropagated)`. -/
def OnlineReachSetAnalyzer.mk?
    (φ : OnlineReachSetAnalyzer.Formula 𝕋 (AtomicProposition S d)) (propagationFrequency : ℕ := 1)
    (dropPropagated : Bool := true) : Option (OnlineReachSetAnalyzer 𝕋 S d) :=
  -- parse(phi,0), with an empty cache
  (OnlineReachSetAnalyzer.parse dropPropagated φ 0 ⟨[], []⟩).map fun st =>
    { propagationFrequency := propagationFrequency, nodes := st.nodes,
      -- obj.leaves = setdiff(1:length(obj.nodes),vertcat(obj.nodes.parents))
      leaves := ((List.range st.nodes.length).map (· + 1)).filter
        (fun i => decide (i ∉ st.nodes.flatMap (·.parents))),
      numObservations := 0,
      -- obj.propagated = false(1,length(obj.nodes))
      propagated := List.replicate st.nodes.length false }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
