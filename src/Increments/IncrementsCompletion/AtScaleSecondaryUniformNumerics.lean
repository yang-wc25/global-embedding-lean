import IncrementsCompletion.AtScaleSecondaryNumerics

/-! Literal secondary cost before every actual datum, signed packet, scale
and finite index. A common genuine frame lower reserve cT0 is the numerical
argument. No finite maximum over packet entries or chart count occurs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance incrementsPositiveFactorySignedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

def incrementsCompletionUniformSecondaryGeometryCost
    (m d N : ℕ) (Tinv Tobs : ℕ → ℝ) (cT0 : ℝ) (q : ℕ) (c : ℝ)
    (InputBudget : ℕ → ℝ) (j : ℕ) : ℝ :=
  round3PreparedGeometryCost m d N Tinv cT0 (1+Tobs 1)
    (actualSecondarySolveOrder q j) (j+1) (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c

theorem incrementsCompletionUniformSecondaryGeometryCost_nonneg
    (m d N : ℕ) (Tinv Tobs : ℕ → ℝ) (cT0 : ℝ) (q : ℕ) (c : ℝ)
    (InputBudget : ℕ → ℝ) (j : ℕ) :
    0 ≤ incrementsCompletionUniformSecondaryGeometryCost m d N Tinv Tobs cT0 q c InputBudget j := by
  unfold incrementsCompletionUniformSecondaryGeometryCost round3PreparedGeometryCost
  exact actualAdaptedUniformGeometryCost_nonneg _ _ _ _ _ _ _ _ _

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletionUniformSecondaryGeometryCost
#print axioms GlobalEmbedding.Continuation.incrementsCompletionUniformSecondaryGeometryCost_nonneg
