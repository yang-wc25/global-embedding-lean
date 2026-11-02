import IncrementsCompletion.PositiveSecondaryDependentFactory

/-! Literal secondary geometry cost for a fixed actual signed packet. It has
no scale/profile-certificate argument. Its dependence on each actual cT is
explicit; no uniform cT lower budget is inferred from positivity alone. -/

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

def incrementsCompletionAtScaleSecondaryGeometryCost
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (Tinv Tobs : ℕ → ℝ) (q : ℕ) (c : ℝ) (InputBudget : ℕ → ℝ) (j : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun a : Sigma (fun r : ActualSecondarySignedRecord (Fin Data.primaryCount) =>
      Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(packet.s r i))) =>
    round3PreparedGeometryCost m d N Tinv (packet.piece a.1 a.2.1 a.2.2).cT (1+Tobs 1)
      (actualSecondarySolveOrder q j) (j+1) (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c)

theorem incrementsCompletionAtScaleSecondaryGeometryCost_nonneg
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (Tinv Tobs : ℕ → ℝ) (q : ℕ) (c : ℝ) (InputBudget : ℕ → ℝ) (j : ℕ) :
    0 ≤ incrementsCompletionAtScaleSecondaryGeometryCost Data hd hs theta packet Tinv Tobs q c InputBudget j :=
  round3PreparedFiniteMaximum_nonneg _

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletionAtScaleSecondaryGeometryCost
#print axioms GlobalEmbedding.Continuation.incrementsCompletionAtScaleSecondaryGeometryCost_nonneg
