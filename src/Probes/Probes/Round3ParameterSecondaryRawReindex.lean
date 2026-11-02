import Probes.Round3PreparedParameterRawPiece

/-! Reindex only the spatial observer list of one actual native piece.
The fixed parameter chart, all actual samples, the physical choice and every
quantitative profile stay literal. In particular Prod.fst repeats source
observers without mixing any parameter coordinates. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

def round3Parameter_secondary_raw_piece_reindex
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    {Index NewIndex : Type*} (observer : Index → OpenPartialHomeomorph M D) (Samples : Index → Set X)
    (piece : Round3PreparedParameterRawPiece Data hd hs i r W observer Samples)
    (reindex : NewIndex → Index) :
    Round3PreparedParameterRawPiece Data hd hs i r W (observer ∘ reindex) (Samples ∘ reindex) := {
  piece with
  observer_samples := fun v => piece.observer_samples (reindex v)
  observer_jets := fun ell hell hell1 v => piece.observer_jets ell hell hell1 (reindex v) }

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_raw_piece_reindex
