import Repair.ReferenceOriginalInteractionGeometry
import Probes.Round3ParameterNativeParent

/-! The actual parameter-lifted parent inherits the original fixed collar.
The collar is transported from the original product chart, without taking
a new compact minimum over the selected primary or secondary pieces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)

theorem repair_reference_original_parent_collar
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (theta : P × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hSmooth : ContMDiff IJ 𝓘(ℝ,ℝ) ∞ theta)
    (K U : Set X) (center : X) (R buffer : ℝ)
    (hSupport : tsupport theta ⊆
      ((Data.parameterChart i.2).prod (Data.atlas.chart i.1)).source ∩
      ((Data.parameterChart i.2).prod (Data.atlas.chart i.1)) ⁻¹' K)
    (hK : K ⊆ closedBall center R) (hBuffer : ∀ z ∈ K, ball z buffer ⊆ U) :
    let thetaN := round3ParameterNativeParent (Data.parameterChart i.2) theta
    let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
    tsupport thetaN ⊆ (Data.parameterChart i.2).target ×ˢ (Data.atlas.chart i.1).source ∧
      (∀ z ∈ tsupport thetaN, ball (q z) buffer ⊆ U) ∧
      q '' tsupport thetaN ⊆ closedBall center R := by
  intro thetaN q
  have hNative := round3Parameter_native_compact_parent (Data.parameterChart i.2)
    (hd.parameter_charts_smooth i.2) theta hCompact hSmooth
    (fun z hz => ⟨(hSupport hz).1.1,mem_univ _⟩)
  constructor
  · intro z hz
    obtain ⟨y,hy,rfl⟩ := hNative.2.2 hz
    exact ⟨(Data.parameterChart i.2).map_source (hSupport hy).1.1,(hSupport hy).1.2⟩
  constructor
  · intro z hz
    obtain ⟨y,hy,rfl⟩ := hNative.2.2 hz
    exact hBuffer _ (hSupport hy).2
  · rintro z ⟨y,hy,rfl⟩
    obtain ⟨w,hw,rfl⟩ := hNative.2.2 hy
    exact hK (hSupport hw).2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_parent_collar
