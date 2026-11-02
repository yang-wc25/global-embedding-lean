import Probes.Round3ParameterPreparedPrimaryLift
import Probes.Round3ParameterNativeParent

/-! Each real native refinement cutoff returns to P with the SAME compact
physical parent. Its global smoothness and chart support are proved through
that parent, so no Hausdorff assumption on P or new output cutoff is needed. -/

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
local notation "𝓙" => 𝓘(ℝ,D)

def round3ParameterLiftedPrimaryCutoff
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) : P × M → ℝ :=
  round3ParameterSupportedPullback (round3ParameterProductChart (Data.parameterChart ip)) piece.cutoff

theorem round3ParameterLiftedPrimaryCutoff_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × M) :
    round3ParameterLiftedPrimaryCutoff Data ip nu W piece z =
      if z.1 ∈ (Data.parameterChart ip).source then piece.cutoff ((Data.parameterChart ip) z.1,z.2) else 0 := by
  simp only [round3ParameterLiftedPrimaryCutoff,round3ParameterSupportedPullback,
    round3ParameterProductChart,OpenPartialHomeomorph.prod_source,
    OpenPartialHomeomorph.refl_source,mem_prod,mem_univ,and_true,
    OpenPartialHomeomorph.prod_apply,OpenPartialHomeomorph.refl_apply,id_eq]

theorem round3Parameter_original_primary_cutoff
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W)
    (theta : P × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hSupport : tsupport theta ⊆ (Data.parameterChart ip).source ×ˢ (univ : Set M))
    (hNative : tsupport (round3ParameterNativeParent (Data.parameterChart ip) theta) ⊆
      (round3ParameterProductChart (M := M) (Data.parameterChart ip)) '' tsupport theta)
    (hParent : tsupport piece.cutoff ⊆ tsupport (round3ParameterNativeParent (Data.parameterChart ip) theta)) :
    ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (round3ParameterLiftedPrimaryCutoff Data ip nu W piece) ∧
    IsCompact (tsupport (round3ParameterLiftedPrimaryCutoff Data ip nu W piece)) ∧
    tsupport (round3ParameterLiftedPrimaryCutoff Data ip nu W piece) ⊆ tsupport theta ∧
    tsupport (round3ParameterLiftedPrimaryCutoff Data ip nu W piece) ⊆
      (round3ParameterLiftedPrimaryChart Data ip nu W piece).source := by
  let q := round3ParameterProductChart (M := M) (Data.parameterChart ip)
  have hCarrier : ∀ z ∈ q.source, q z ∈ tsupport piece.cutoff → z ∈ tsupport theta := by
    intro z hz he
    exact round3Parameter_native_parent_source (Data.parameterChart ip) theta
      hSupport hNative z hz.1 (hParent he)
  have hSub := round3ParameterSupportedPullback_support q piece.cutoff
    (tsupport theta) (isClosed_tsupport _) hCarrier
  refine ⟨round3ParameterSupportedPullback_smooth q piece.cutoff (tsupport theta)
      (isClosed_tsupport _) hSupport hCarrier
      (round3ParameterProductChart_smooth (Data.parameterChart ip) (hd.parameter_charts_smooth ip))
      piece.smooth.contMDiffOn,
    hCompact.of_isClosed_subset (isClosed_tsupport _) hSub,hSub,?_⟩
  intro z hz
  have hzs := hSupport (hSub hz)
  have hNativeEta := (round3ParameterSupportedPullback_tsupport_iff q piece.cutoff z hzs).mp hz
  apply (round3ParameterChartPullback_source_iff (Data.parameterChart ip).symm
    (actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native)
    (fun y hy => (piece.data.2.2.2.1 y hy).1) z hzs.1).mpr
  exact piece.support hNativeEta

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_primary_cutoff
