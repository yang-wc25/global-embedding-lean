import Probes.Round3ParameterWholeReferenceProfiles
import Smoothing.Round3ParameterCompactParents

/-! The same original raw parameter/source preparation supplies the actual
reference carrier samples.  Every parameter chart's piece is measured in
that chart's original parameter norm domain; no one-chart cover assumption
or identity parameter chart is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
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
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_product_parent_original_samples
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (B : TensorBufferedChartFamily (Fin Ref.parameterCount) P Ep)
    (hChart : B.chart = Ref.parameterChart)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Ref.atlas BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B Ref.parameterSet BP0 TP0 Dp)
    (hSampling : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Ref.parameterNormDomain i) :
    let theta := round3ParameterProductParent Ref.atlas B
      (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    ∀ i z, z ∈ tsupport (theta i) →
      z.1 ∈ (Ref.parameterChart i.2).source ∧ z.2 ∈ Ref.atlas.inner i.1 ∧
        (Ref.parameterChart i.2) z.1 ∈ Ref.parameterNormDomain i.2 := by
  intro theta i z hz
  have hProd := parameterLocalProductCutoff_tsupport_subset Ref.atlas B
    (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw) i
    (round3ParameterProductParent_tsupport Ref.atlas B _ _ i hz)
  have hp := RP.inner_support i.2 (tensorLocalNormalizedCutoff_tsupport_subset RP.raw i.2 hProd.1)
  have hx := RS.inner_support i.1 (squareNormalizedCutoff_tsupport_subset RS.raw i.1 hProd.2)
  rw [← hChart]
  exact ⟨B.inner_subset i.2 hp,hx,
    hSampling i.2 (tensorLocalInner_subset_sampling B i.2 (tensorLocalInner_mem B i.2 hp))⟩

variable [T2Space M]

theorem round3Parameter_whole_primary_original_carriers
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSampling : ∀ i z, z ∈ tsupport (theta i) →
      z.1 ∈ (Ref.parameterChart i.2).source ∧ z.2 ∈ Ref.atlas.inner i.1 ∧
        (Ref.parameterChart i.2) z.1 ∈ Ref.parameterNormDomain i.2) :
    ∀ nu i a y, y ∈ tsupport (packet.piece nu i a).cutoff →
      y.2 ∈ Ref.atlas.inner (packet.piece nu i a).host ∧ y.1 ∈ Ref.parameterNormDomain i.2 := by
  intro nu i a y hy
  have hSupport : tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M) :=
    fun z hz => ⟨(hSampling i z hz).1,mem_univ _⟩
  have hNative := round3Parameter_native_compact_parent (Ref.parameterChart i.2)
    (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i) hSupport
  obtain ⟨z,hz,rfl⟩ := hNative.2.2 (packet.native_parent nu i a hy)
  rw [packet.host]
  exact ⟨(hSampling i z hz).2.1,(hSampling i z hz).2.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_product_parent_original_samples
#print axioms GlobalEmbedding.Continuation.round3Parameter_whole_primary_original_carriers
