import Upgrade.RankQResidualNorms

/-! Explicit inherited operator norms for derivatives of the actual Schur
residual. These are compiled native-instance terms, not new norm choices. -/
noncomputable section
namespace GlobalEmbedding.Upgrade
variable {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

@[instance_reducible]
def rankQDerivativeNormedAddCommGroup (B : S →L[ℝ] W) :
    NormedAddCommGroup ((S →L[ℝ] W) →L[ℝ] (B.ker →L[ℝ] B.rangeᗮ)) := by
  let : NormedAddCommGroup B.ker := inferInstance
  let : NormedSpace ℝ B.ker := inferInstance
  let : NormedAddCommGroup B.rangeᗮ := inferInstance
  let : NormedSpace ℝ B.rangeᗮ := inferInstance
  let : NormedAddCommGroup (B.ker →L[ℝ] B.rangeᗮ) := rankQResidualNormedAddCommGroup B
  let : NormedSpace ℝ (B.ker →L[ℝ] B.rangeᗮ) := rankQResidualNormedSpace B
  exact ContinuousLinearMap.toNormedAddCommGroup
end GlobalEmbedding.Upgrade
