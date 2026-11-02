import Probes.Round3PreparedParameterRawPiece

/-!
# Positive-jet actual secondary output

This new internal output keeps every physical field, sample, support, and
numerical geometry cost of the existing raw-piece interface. Its chart and
inverse estimates state only the positive derivative orders consumed by
the original prepared secondary family. The cutoff bound still includes
zero. The old record and all original theorem types are unchanged.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

structure IncrementsCompletionPositiveParameterRawPiece
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (W : Set (Ep × M)) {Index : Type*} (observer : Index → OpenPartialHomeomorph M D)
    (Samples : Index → Set X) where
  choice : ActualOriginalSecondaryChoice Ep M m
  carrier : Set (Ep × M)
  sample : Set X
  host_eq : choice.host = Data.atlas.chart i.1
  cutoff_smooth : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ choice.cutoff W
  carrier_eq : carrier = tsupport choice.cutoff ∩
    actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W
  sample_subset : sample ⊆ choice.chart.target
  carrier_source : carrier ⊆ choice.chart.source
  source_domain : choice.chart.source ⊆ W
  chart_smooth : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ choice.chart choice.chart.source
  chart_inverse_smooth : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ choice.chart.symm choice.chart.target
  host_source : choice.chart.source ⊆ ((OpenPartialHomeomorph.refl Ep).prod choice.host).source
  support : tsupport (fun y : W => choice.cutoff y.val) ∩ Subtype.val ⁻¹'
    actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W ⊆ Subtype.val ⁻¹' carrier
  pair : carrier ⊆ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W
  cut_smooth : let b := (OpenPartialHomeomorph.refl Ep).prod choice.host
    ContDiffOn ℝ ∞ (choice.cutoff ∘ b.symm) (b.symm.trans choice.chart).source
  inv_smooth : let b := (OpenPartialHomeomorph.refl Ep).prod choice.host
    ContDiffOn ℝ ∞ (b.symm.trans choice.chart).symm (b.symm.trans choice.chart).target
  host_samples : let b := (OpenPartialHomeomorph.refl Ep).prod choice.host
    (b.symm.trans choice.chart).symm '' sample ⊆ (parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i
  observer_samples : ∀ v z, z ∈ Samples v ∩
    (fun z : X => (z.1,(observer v).symm z.2)) ⁻¹' carrier →
    choice.chart (z.1,(observer v).symm z.2) ∈ sample
  Tinv : ℕ → ℝ
  Kcut : ℕ → ℝ
  Tobs : ℕ → ℝ
  Tinv_nonneg : ∀ k, 0 ≤ Tinv k
  Kcut_nonneg : ∀ k, 0 ≤ Kcut k
  Tobs_nonneg : ∀ k, 0 ≤ Tobs k
  cut_jets : ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ n k, k ≤ n → ∀ z ∈ sample,
    let b := (OpenPartialHomeomorph.refl Ep).prod choice.host
    ell^k*‖iteratedFDeriv ℝ k (choice.cutoff ∘ b.symm) ((b.symm.trans choice.chart).symm z)‖ ≤ Kcut n
  inv_jets : ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ k, 1 ≤ k → ∀ z, z ∈ sample →
    let b := (OpenPartialHomeomorph.refl Ep).prod choice.host
    ell^(k-1)*‖iteratedFDeriv ℝ k (b.symm.trans choice.chart).symm z‖ ≤ Tinv k
  observer_jets : ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ v z,
    z ∈ Samples v ∩ (fun z : X => (z.1,(observer v).symm z.2)) ⁻¹' carrier → ∀ k, 1 ≤ k →
    ell^(k-1)*‖iteratedFDeriv ℝ k
      (choice.chart ∘ (fun z : X => (z.1,(observer v).symm z.2))) z‖ ≤ Tobs k
  cT : ℝ
  Bnative : ℝ
  cT_pos : 0 < cT
  Bnative_pos : 0 < Bnative
  produce : ∀ (n j : ℕ) (ell budget c : ℝ), 0 < ell → ell ≤ 1 →
    IncrementsOriginalCoordinateEllipticityInputs Data c →
    incrementsOriginalCoreInputProfile Data (max n j) ell ≠ ⊤ →
    (incrementsOriginalCoreInputProfile Data (max n j) ell).toReal ≤ budget →
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    ∃ out : ActualSecondaryRawGeometry F hF n j ell
      (round3PreparedGeometryCost m d N Tinv cT Bnative n j budget c) W,
      out.c = choice.c ∧ out.chart = choice.chart ∧
      out.phase = actualOriginalParameterSignedPhase Data i r.val ∧
      out.sample = sample ∧ out.support = carrier

def incrementsCompletion_positive_secondary_piece_reindex
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    {Index NewIndex : Type*} (observer : Index → OpenPartialHomeomorph M D) (Samples : Index → Set X)
    (piece : IncrementsCompletionPositiveParameterRawPiece Data hd hs i r W observer Samples)
    (reindex : NewIndex → Index) :
    IncrementsCompletionPositiveParameterRawPiece Data hd hs i r W (observer ∘ reindex) (Samples ∘ reindex) := {
  piece with
  observer_samples := fun v => piece.observer_samples (reindex v)
  observer_jets := fun ell hell hell1 v => piece.observer_jets ell hell hell1 (reindex v) }

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.IncrementsCompletionPositiveParameterRawPiece
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_positive_secondary_piece_reindex
