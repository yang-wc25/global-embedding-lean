import Mathlib.Data.Nat.Basic

/-!
# Dimensions in the closed parallelizable result

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 108–115;
DAG node `immersion-target-dimension`.
-/

namespace GlobalEmbedding.Paper

/-- The paper's `s_n = n(n+1)/2`, the dimension of symmetric two-tensors in dimension `n`.
Source: `literature/parallelizable-stable-plus-one/main.tex`, line 108. -/
def symmetricTensorDimension (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The Euclidean ambient dimension `s_n + 1` in the closed parallelizable theorem.
Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 108–115. -/
def closedAmbientDimension (n : ℕ) : ℕ := symmetricTensorDimension n + 1

end GlobalEmbedding.Paper
