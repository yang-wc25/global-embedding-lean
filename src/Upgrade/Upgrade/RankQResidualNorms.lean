import Upgrade.RankQSchur

/-!
# Explicit inherited norms for the actual Schur residual

These definitions expose the existing subtype and operator norms as compiled
terms. They do not select a new norm. Instantiating their generic arguments
prevents Lean from repeatedly expanding the actual quotient second form while
searching for deeply nested native typeclass instances.
-/

noncomputable section
namespace GlobalEmbedding.Upgrade

variable {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

@[instance_reducible]
def rankQResidualNormedAddCommGroup (B : S →L[ℝ] W) :
    NormedAddCommGroup (B.ker →L[ℝ] B.rangeᗮ) := inferInstance

@[instance_reducible]
def rankQResidualNormedSpace (B : S →L[ℝ] W) :
    NormedSpace ℝ (B.ker →L[ℝ] B.rangeᗮ) := inferInstance

@[instance_reducible]
def rankQResidualFiniteDimensional (B : S →L[ℝ] W) :
    FiniteDimensional ℝ (B.ker →L[ℝ] B.rangeᗮ) := inferInstance

end GlobalEmbedding.Upgrade
