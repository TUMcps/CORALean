# nn/layers

CORA methods of `nn/layers/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NN/`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `backpropZonotopeBatch` | — | — |  |
| `computeApproxPoly` | — | — |  |
| `evaluateConZonotope` | — | — |  |
| `evaluatePolyZonotope` | — | — |  |
| `evaluatePolyZonotopeNeuron` | — | — |  |
| `evaluateTaylm` | — | — |  |
| `evaluateZonotopeBatch` | — | — |  |
| `findRegionPolys` | — | — |  |
| `getMergeBuckets` | — | — |  |
| `instantiateFromString` | — | — |  |
| `nnActLayerFromHandle` | — | — |  |
| `nnActivationLayer` | float | [`Layer.activation_sound`](../../../src/CORALean/NN/Layers/Theorems/ActivationSound.lean), [`Layer.activation`](../../../src/CORALean/NN/Layers/Operations/Activation.lean) | route b — soundness stated for any `FloatOps 𝕋`; the layer runs at `Dyadic` (`Examples/RunnableFloat.lean`) |
| `nnAvgPool2DLayer` | float | [`Layer.avgPool_sound`](../../../src/CORALean/NN/Layers/Theorems/AvgPoolSound.lean), [`Layer.avgPool`](../../../src/CORALean/NN/Layers/Operations/AvgPool.lean) | route b — soundness stated for any `FloatOps 𝕋`; the layer runs at `Dyadic` (`Examples/RunnableFloat.lean`) |
| `nnBatchNormLayer` | float | [`Layer.batchNorm_sound`](../../../src/CORALean/NN/Layers/Theorems/BatchNormSound.lean), [`Layer.batchNorm_sound`](../../../src/CORALean/NN/Layers/Theorems/Real/BatchNormSound.lean), [`Layer.batchNorm`](../../../src/CORALean/NN/Layers/Operations/BatchNorm.lean) | route b — soundness stated for any `FloatOps 𝕋`; the layer runs at `Dyadic` (`Examples/RunnableFloat.lean`) |
| `nnCompositeLayer` | float | [`Layer.comp_sound`](../../../src/CORALean/NN/Layers/Layer.lean), [`Layer.comp`](../../../src/CORALean/NN/Layers/Layer.lean) | route b — stated for any set representation, no scalar named; the float layers instantiate it (`Examples/RunnableFloat.lean`) |
| `nnConv2DLayer` | float | [`Layer.conv_sound`](../../../src/CORALean/NN/Layers/Theorems/ConvSound.lean), [`Layer.conv`](../../../src/CORALean/NN/Layers/Operations/Conv.lean) | route b — soundness stated for any `FloatOps 𝕋`; the layer runs at `Dyadic` (`Examples/RunnableFloat.lean`) |
| `nnConvTranspose2DLayer` | — | — |  |
| `nnElementwiseAffineLayer` | — | — |  |
| `nnExpLayer` | — | — |  |
| `nnGCNLayer` | proved | [`GNN.gcn_exact`](../../../src/CORALean/NN/Graph/Theorems/ConvExact.lean), [`GNN.gcn_exact_of_adjacency`](../../../src/CORALean/NN/Graph/Theorems/ConvExactOfAdjacency.lean) |  |
| `nnGNNGlobalPoolingLayer` | proved | [`GNN.sumPool_exact`](../../../src/CORALean/NN/Graph/Theorems/PoolingExact.lean) |  |
| `nnGNNLayer` | — | — |  |
| `nnGNNLinearLayer` | — | — |  |
| `nnGNNProjectionLayer` | — | — |  |
| `nnGeneratorReductionLayer` | — | — |  |
| `nnGroupSortLayer` | — | — |  |
| `nnIdentityLayer` | float | [`Layer.identity_sound`](../../../src/CORALean/NN/Layers/Layer.lean), [`Layer.identity`](../../../src/CORALean/NN/Layers/Layer.lean) | route b — stated for any set representation, no scalar named; the float layers instantiate it (`Examples/RunnableFloat.lean`) |
| `nnInvSqrtRootLayer` | proved | [`invSqrtRelaxation_sound`](../../../src/CORALean/NN/Layers/Theorems/Real/InvSqrtRelaxationSound.lean) |  |
| `nnLayer` | float | [`Layer`](../../../src/CORALean/NN/Layers/Layer.lean) | route b — stated for any set representation, no scalar named; the float layers instantiate it (`Examples/RunnableFloat.lean`) |
| `nnLeakyReLULayer` | — | — |  |
| `nnLinearLayer` | float | [`Layer.linear_exact`](../../../src/CORALean/NN/Theorems/Real/LinearExact.lean), [`Layer.linear_sound`](../../../src/CORALean/NN/Layers/Theorems/LinearSound.lean), [`Layer.linear`](../../../src/CORALean/NN/Layers/Operations/Linear.lean) | route b — soundness stated for any `FloatOps 𝕋`; the layer runs at `Dyadic` (`Examples/RunnableFloat.lean`) |
| `nnLipConstrLinearLayer` | — | — |  |
| `nnMaxPool2DLayer` | float | [`Layer.maxPool_sound`](../../../src/CORALean/NN/Layers/Theorems/MaxPoolSound.lean), [`Layer.maxPool`](../../../src/CORALean/NN/Layers/Operations/MaxPool.lean) | route b — soundness stated for any `FloatOps 𝕋`; the layer runs at `Dyadic` (`Examples/RunnableFloat.lean`) |
| `nnReLULayer` | float | [`reluRelaxation`](../../../src/CORALean/NN/Layers/Operations/ReluRelaxation.lean), [`Layer.relu_sound`](../../../src/CORALean/NN/Layers/Theorems/ReluSound.lean), [`reluRelaxation_sound`](../../../src/CORALean/NN/Layers/Theorems/ReluRelaxationSound.lean) | route b — soundness stated for any `FloatOps 𝕋`; the layer runs at `Dyadic` (`Examples/RunnableFloat.lean`) |
| `nnReshapeLayer` | float | [`Layer.reshape_exact`](../../../src/CORALean/NN/Layers/Theorems/ReshapeExact.lean), [`Layer.reshape_sound`](../../../src/CORALean/NN/Layers/Theorems/ReshapeSound.lean), [`Layer.reshape`](../../../src/CORALean/NN/Layers/Operations/Reshape.lean) | route b — stated for any set representation, no scalar named; the float layers instantiate it (`Examples/RunnableFloat.lean`) |
| `nnRootLayer` | — | — |  |
| `nnSShapeLayer` | — | — |  |
| `nnSigmoidLayer` | float | [`Layer.sigmoid_sound`](../../../src/CORALean/NN/Layers/Theorems/SigmoidSound.lean), [`sigmoidRelaxation_sound`](../../../src/CORALean/NN/Layers/Theorems/Real/SigmoidRelaxationSound.lean), [`sigmoidRelaxation_sound`](../../../src/CORALean/NN/Layers/Theorems/SigmoidRelaxationSound.lean), [`Layer.sigmoid`](../../../src/CORALean/NN/Layers/Operations/Sigmoid.lean) | route b — soundness stated for any `FloatOps 𝕋`; the layer runs at `Dyadic` (`Examples/RunnableFloat.lean`) |
| `nnSoftPlusLayer` | — | — |  |
| `nnSoftmaxLayer` | float | [`Layer.softmax_sound`](../../../src/CORALean/NN/Layers/Theorems/Real/SoftmaxSound.lean), [`Layer.softmax_sound`](../../../src/CORALean/NN/Layers/Theorems/SoftmaxSound.lean), [`Layer.softmax`](../../../src/CORALean/NN/Layers/Operations/Softmax.lean) | route b — soundness stated for any `FloatOps 𝕋`; the layer runs at `Dyadic` (`Examples/RunnableFloat.lean`) |
| `nnSquareLayer` | — | — |  |
| `nnTanhLayer` | float | [`Layer.tanh_sound`](../../../src/CORALean/NN/Layers/Theorems/TanhSound.lean), [`tanhRelaxation_sound`](../../../src/CORALean/NN/Layers/Theorems/Real/TanhRelaxationSound.lean), [`tanhRelaxation_sound`](../../../src/CORALean/NN/Layers/Theorems/TanhRelaxationSound.lean), [`Layer.tanh`](../../../src/CORALean/NN/Layers/Operations/Tanh.lean) | route b — soundness stated for any `FloatOps 𝕋`; the layer runs at `Dyadic` (`Examples/RunnableFloat.lean`) |
| `nnVisualizationLayer` | out-of-scope | n/a — plotting/display |  |
