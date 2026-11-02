import IncrementsCompletion.PositiveSecondaryPacketProfiles

/-! Current-scale true packet profiles, with numeric budgets explicit before
the certificate. The chart bounds use positive orders and cutoff bounds keep
order zero. No geometric fields, sample domains or signs are changed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
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
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

structure IncrementsCompletionAtScaleSecondaryPacketProfiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (ell : ℝ) (Tinv Kcut Tobs : ℕ → ℝ) : Prop where
  positive : ∀ r i (a : packet.s r i) observer k, 1 ≤ k →
    let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
    let native := (choice.pullback (Data.parameterChart observer.2)).toNative
    let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans native.chart
    ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
      ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2) ∈
        round3PreparedParameterSecondaryCarrier Data r choice →
      ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Tobs k ∧
      ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Tinv k
  cutoff : ∀ r i (a : packet.s r i) observer n k, k ≤ n →
    let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
    ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
      ell^k*‖iteratedFDeriv ℝ k (fun y : X => choice.cutoff
        ((Data.parameterChart observer.2).symm y.1,(Data.atlas.chart observer.1).symm y.2)) z‖ ≤ Kcut n

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.IncrementsCompletionAtScaleSecondaryPacketProfiles
