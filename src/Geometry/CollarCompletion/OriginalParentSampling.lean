import Repair.SourceCollarNovParameterLocalizedParents
import Probes.ActualIncrementOriginalSampling

/-!
# Original parent supports put the actual owner point in the original samples

The raw source and local parameter preparations are used literally. The
parent is exactly `sourceCollarNovParameterLocalized psi` applied to the
existing square product parent. Its topological support lies in both original
inners, so the original sampling inclusions put the actual owner coordinates
in the original Omega and Q. No compactness, support enlargement, norm-domain
replacement, or whole-open-chart inclusion in Q is required.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.CollarCompletion

variable {n d c N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- The exact localized original product parent retains the parameter
inner as well as the source inner. -/
theorem original_parameter_localized_parent_inner
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (K : Set P) (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation A BS TS Ds)
    (RP : TensorLocalRawPreparation B K BP TP Dp)
    (psi : P → ℝ) (i : Fin A.count × Fin c) :
    let theta := round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    tsupport (sourceCollarNovParameterLocalized psi (theta i)) ⊆ B.inner i.2 ×ˢ A.inner i.1 := by
  intro theta z hz
  have hp := (sourceCollarNov_parameter_localized_tsupport psi (theta i) hz).1
  have ho := round3ParameterProductParent_tsupport A B
    (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw) i hp
  have hc := parameterLocalProductCutoff_tsupport_subset A B
    (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw) i ho
  exact ⟨RP.inner_support i.2 (tensorLocalNormalizedCutoff_tsupport_subset RP.raw i.2 hc.1),
    RS.inner_support i.1 (squareNormalizedCutoff_tsupport_subset RS.raw i.1 hc.2)⟩

/-- Every point of that literal support is seen in the unchanged original
parameter and source sampling domains at its owner coordinates. -/
theorem original_parameter_localized_parent_own_samples
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (K : Set P) (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation A BS TS Ds)
    (RP : TensorLocalRawPreparation B K BP TP Dp)
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep)
    (hSource : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i)
    (psi : P → ℝ) (i : Fin A.count × Fin c) (z : P × M) :
    let theta := round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    z ∈ tsupport (sourceCollarNovParameterLocalized psi (theta i)) →
      z.1 ∈ (B.chart i.2).source ∧ z.2 ∈ (A.chart i.1).source ∧
      B.chart i.2 z.1 ∈ Q i.2 ∧ A.chart i.1 z.2 ∈ Omega i.1 := by
  intro theta hz
  have hi := original_parameter_localized_parent_inner A B K BS TS BP TP Ds Dp RS RP psi i hz
  exact ⟨B.inner_subset i.2 hi.1,A.inner_subset i.1 hi.2,
    hParameter i.2 (tensorLocalInner_subset_sampling B i.2 (tensorLocalInner_mem B i.2 hi.1)),
    hSource i.1 (bufferedInner_subset_sampling A i.1 (bufferedInnerCoordinates_mem A i.1 hi.2))⟩

/-- This is precisely the host membership needed by the pointwise
observer composition estimate. The observer coordinates are not changed. -/
theorem original_parameter_localized_parent_observer_samples
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (K : Set P) (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation A BS TS Ds)
    (RP : TensorLocalRawPreparation B K BP TP Dp)
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep)
    (hSource : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i)
    (psi : P → ℝ) (owner observer : Fin A.count × Fin c) (z : Ep × D) :
    let theta := round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ((B.chart observer.2).symm z.1,(A.chart observer.1).symm z.2) ∈
      tsupport (sourceCollarNovParameterLocalized psi (theta owner)) →
    B.chart owner.2 ((B.chart observer.2).symm z.1) ∈ Q owner.2 ∧
      A.chart owner.1 ((A.chart observer.1).symm z.2) ∈ Omega owner.1 := by
  intro theta hz
  exact (original_parameter_localized_parent_own_samples A B K BS TS BP TP Ds Dp RS RP
    Omega Q hSource hParameter psi owner _ hz).2.2

/-- The exact supported native parent gives the same original physical
point. Its source condition is only the actual observer chart target. -/
theorem original_parameter_localized_native_parent_own_samples
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (K : Set P) (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation A BS TS Ds)
    (RP : TensorLocalRawPreparation B K BP TP Dp)
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep)
    (hSource : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i)
    (psi : P → ℝ) (owner : Fin A.count × Fin c) (observer : Fin c)
    (z : Ep × M) (hz : z.1 ∈ (B.chart observer).target) :
    let theta := round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    z ∈ tsupport (round3ParameterNativeParent (B.chart observer)
      (sourceCollarNovParameterLocalized psi (theta owner))) →
    B.chart owner.2 ((B.chart observer).symm z.1) ∈ Q owner.2 ∧
      A.chart owner.1 z.2 ∈ Omega owner.1 := by
  intro theta hs
  have hp := (round3ParameterSupportedPullback_tsupport_iff
    (round3ParameterProductChart (M := M) (B.chart observer)).symm
    (sourceCollarNovParameterLocalized psi (theta owner)) z ⟨hz,mem_univ _⟩).mp hs
  exact (original_parameter_localized_parent_own_samples A B K BS TS BP TP Ds Dp RS RP
    Omega Q hSource hParameter psi owner _ hp).2.2

/-- Original native datum specialization. All Omega/Q fields and parameter
chart equalities in the result are the original ones, without compactness. -/
theorem original_parameter_localized_parent_original_samples
    (Data : IncrementsOriginalNativeData n d N M P)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (psi : P → ℝ) (owner observer : Fin Data.atlas.count × Fin Data.parameterCount) (z : Ep × D) :
    let theta := round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2) ∈
      tsupport (sourceCollarNovParameterLocalized psi (theta owner)) →
    Data.parameterChart owner.2 ((Data.parameterChart observer.2).symm z.1) ∈
      Data.parameterNormDomain owner.2 ∧
      Data.atlas.chart owner.1 ((Data.atlas.chart observer.1).symm z.2) ∈ Data.sourceNormDomain owner.1 := by
  intro theta hz
  have h := original_parameter_localized_parent_own_samples Data.atlas B Data.parameterSet
    BS TS BP TP Ds Dp RS RP Data.sourceNormDomain Data.parameterNormDomain hSource hParameter
    psi owner ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2) hz
  simpa only [hChart] using h.2.2

end GlobalEmbedding.Continuation.CollarCompletion
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_parameter_localized_parent_inner
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_parameter_localized_parent_own_samples
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_parameter_localized_native_parent_own_samples
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_parameter_localized_parent_original_samples
