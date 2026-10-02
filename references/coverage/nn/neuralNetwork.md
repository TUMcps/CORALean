# nn/@neuralNetwork

CORA methods of `nn/@neuralNetwork/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NN/`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `addVisualizationLayers` | out-of-scope | n/a — plotting/display |  |
| `backprop` | proved | [`Chain.backprop`](../../../src/CORALean/NN/Operations/Backprop.lean), [`Chain.backprop_eq_transpose_mulVec`](../../../src/CORALean/NN/Theorems/BackpropEqTranspose.lean), [`Chain.backprop_eq_fderiv_transpose`](../../../src/CORALean/NN/Theorems/BackpropEqFDerivTranspose.lean) | point gradient only: backprop is the transposed Jacobian `(sensitivity x)ᵀ g`, and `(D eval x)ᵀ g` where every layer is differentiable; the interval and zonotope batch variants stay `—` |
| `backpropIntervalBatch` | — | — |  |
| `backpropZonotopeBatch` | — | — |  |
| `backpropZonotopeBatch_` | — | — |  |
| `calcSensitivity` | proved | [`Chain.sensitivity`](../../../src/CORALean/NN/Operations/Sensitivity.lean), [`Chain.sensitivity_eq_fderiv`](../../../src/CORALean/NN/Theorems/SensitivityFDeriv.lean), [`Layer.sensitivity_eq_of_hasFDerivAt`](../../../src/CORALean/NN/Theorems/SensitivityOfMatrix.lean) |  |
| `castWeights` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `clearVisualizationLayerPlots` | out-of-scope | n/a — plotting/display |  |
| `computeFGSMAttack` | — | — |  |
| `computePGDAttack` | — | — |  |
| `computeReducedNetwork` | float | [`reduceOnTheFly`](../../../src/CORALean/NN/Operations/ReduceOnTheFly.lean), [`reduceOnTheFlyFrom`](../../../src/CORALean/NN/Operations/ReduceOnTheFlyFrom.lean), [`neuronMerging_network_outer`](../../../src/CORALean/NN/Theorems/NeuronMergingNetworkOuter.lean), [`neuronMerging_sandwich_outer`](../../../src/CORALean/NN/Theorems/NeuronMergingOuter.lean), [`reduceOnTheFly_outer`](../../../src/CORALean/NN/Theorems/ReduceOnTheFlyOuter.lean) | route b — `reduceOnTheFly` and its soundness are stated for any `FloatOps 𝕋`, computable |
| `convertDLToolboxNetwork` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `convertToDLToolboxNetwork` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `copyNeuralNetwork` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `enumerateLayers` | — | — |  |
| `evaluate` | proved | [`Chain.eval`](../../../src/CORALean/NN/Operations/ChainEval.lean), [`NeuralNetwork.eval`](../../../src/CORALean/NN/Operations/Eval.lean), [`RefinableNetwork.eval`](../../../src/CORALean/NN/Operations/RefinableNetworkEval.lean), [`NeuralNetwork.sound_eval`](../../../src/CORALean/NN/Theorems/SoundEval.lean) |  |
| `evaluateZonotopeBatch` | float | [`NeuralNetwork.enclose`](../../../src/CORALean/NN/Operations/Enclose.lean), [`NeuralNetwork.Sound.enclose_outer`](../../../src/CORALean/NN/Theorems/EncloseOuter.lean), [`NeuralNetwork.enclose_outer`](../../../src/CORALean/NN/Theorems/EncloseOuterEval.lean) | route b — stated for any set representation, no scalar named; the float layers instantiate it (`Examples/RunnableFloat.lean`) |
| `evaluateZonotopeBatch_` | float | [`NeuralNetwork.enclose`](../../../src/CORALean/NN/Operations/Enclose.lean), [`NeuralNetwork.Sound.enclose_outer`](../../../src/CORALean/NN/Theorems/EncloseOuter.lean), [`NeuralNetwork.enclose_outer`](../../../src/CORALean/NN/Theorems/EncloseOuterEval.lean) | route b — stated for any set representation, no scalar named; the float layers instantiate it (`Examples/RunnableFloat.lean`) |
| `evaluate_` | float | [`NeuralNetwork.enclose`](../../../src/CORALean/NN/Operations/Enclose.lean), [`NeuralNetwork.Sound.enclose_outer`](../../../src/CORALean/NN/Theorems/EncloseOuter.lean), [`NeuralNetwork.enclose_outer`](../../../src/CORALean/NN/Theorems/EncloseOuterEval.lean) | route b — stated for any set representation, no scalar named; the float layers instantiate it (`Examples/RunnableFloat.lean`) |
| `explain` | proved | [`explanationRefineLoop`](../../../src/CORALean/NN/Operations/ExplanationRefineLoop.lean), [`greedyAbstractExplanation`](../../../src/CORALean/NN/Operations/GreedyAbstractExplanation.lean), [`greedyExplanationStep`](../../../src/CORALean/NN/Operations/GreedyExplanationStep.lean), [`explanationRefineLoop_iff`](../../../src/CORALean/NN/Theorems/ExplanationRefineLoopIff.lean), [`greedyAbstractExplanation_eq_greedyMinimalExplanation`](../../../src/CORALean/NN/Theorems/GreedyAbstractExplanationEqGreedyMinimalExplanation.lean), [`minSuffExplanation_iff_counterexample`](../../../src/CORALean/NN/Theorems/MinSuffExplanationCounterexample.lean), [`suffExplanation_of_exact`](../../../src/CORALean/NN/Theorems/SuffExplanationOfExact.lean) |  |
| `exportAsJSON` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `exportAsStruct` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `exportNetworkAsCellArray` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `exportONNXNetwork` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `generateFromString` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getFromCellArray` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `getInputNeuronOrder` | — | — |  |
| `getNormalForm` | — | — |  |
| `getNumMessagePassingSteps` | out-of-scope | n/a — matlab-runtime | a pure count of the network's layers, neurons or parameters (bookkeeping, no set semantics) |
| `getNumNeurons` | out-of-scope | n/a — matlab-runtime | a pure count of the network's layers, neurons or parameters (bookkeeping, no set semantics) |
| `getNumParams` | out-of-scope | n/a — matlab-runtime | a pure count of the network's layers, neurons or parameters (bookkeeping, no set semantics) |
| `getOrderPattern` | — | — |  |
| `getRefinableLayers` | — | — | definition only, no theorem: [`Schedule.refineLayer`](../../../src/CORALean/NN/Operations/RefineLayer.lean) is the refinement step (row `refine`), not the listing of refinable layers |
| `importFromJSON` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `importFromStruct` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `initWeights` | out-of-scope | n/a — random/sampling |  |
| `neuralNetwork` | float | [`NeuralNetwork.sound_eval`](../../../src/CORALean/NN/Theorems/SoundEval.lean), [`Enclose.toLayer_sound`](../../../src/CORALean/NN/Layers/Layer.lean), [`NeuralNetwork.toLayer_sound`](../../../src/CORALean/NN/Theorems/ToLayerSound.lean), [`NeuralNetwork.ofLayer_sound`](../../../src/CORALean/NN/NeuralNetwork.lean), [`NeuralNetwork`](../../../src/CORALean/NN/NeuralNetwork.lean) | route b — stated for any set representation, no scalar named; the float layers instantiate it (`Examples/RunnableFloat.lean`) |
| `nonlinearSysDT` | — | — |  |
| `prepareForZonoBatchEval` | — | — |  |
| `propagateBounds` | — | — |  |
| `readGNNdata` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `readGNNetwork` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `readGNNnetwork` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `readJSONNetwork` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `readNNetNetwork` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `readNetwork` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `readONNXNetwork` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `readSherlockNetwork` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `readYMLNetwork` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `reduceGNNForNode` | — | — |  |
| `refine` | float | [`Schedule.refine`](../../../src/CORALean/NN/Operations/Refine.lean), [`Schedule.refineLoop`](../../../src/CORALean/NN/Operations/RefineLoop.lean), [`RefinableNetwork.image_subset_refine`](../../../src/CORALean/NN/Theorems/ImageSubsetRefine.lean), [`RefinableNetwork.image_subset_refineLoop`](../../../src/CORALean/NN/Theorems/ImageSubsetRefineLoop.lean) | route b — stated for any set representation, no scalar named; the float layers instantiate it (`Examples/RunnableFloat.lean`) |
| `reset` | out-of-scope | n/a — matlab-runtime |  |
| `resetApproxOrder` | out-of-scope | n/a — matlab-runtime |  |
| `resetBounds` | out-of-scope | n/a — matlab-runtime |  |
| `resetGNN` | out-of-scope | n/a — matlab-runtime |  |
| `setInputSize` | out-of-scope | n/a — matlab-runtime |  |
| `train` | — | — |  |
| `verify` | float | [`NeuralNetwork.verifySplit`](../../../src/CORALean/NN/Operations/VerifySplit.lean), [`NeuralNetwork.verifySplit_sound`](../../../src/CORALean/NN/Theorems/VerifySplitSound.lean) | route b — stated for any set representation, no scalar named; the float layers instantiate it (`Examples/RunnableFloat.lean`); verification by input splitting; a `true` verdict is sound whatever the splitter |
| `visLossLandscape` | out-of-scope | n/a — plotting/display |  |
