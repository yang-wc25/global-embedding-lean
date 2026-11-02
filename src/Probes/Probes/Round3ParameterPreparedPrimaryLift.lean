import Probes.Round3PreparedPrimaryPiece
import Probes.Round3ParameterChartPullback

/-! Actual original primary pieces are lifted to the physical parameter
manifold by genuine two-sided parameter-chart conjugation. One common
finite index may contain pieces from EVERY parameter chart. Original phase,
cutoff, free normal and tensor functional are kept literally; only the
subordinate eta is transported, inside the original free datum. -/

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
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def round3ParameterLiftedPrimaryChart
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) :
    OpenPartialHomeomorph (P × M) (P × D) :=
  round3ParameterChartPullback (Data.parameterChart ip).symm
    (actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native)

theorem round3ParameterLiftedPrimaryChart_preserves
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) :
    Round3ParameterChartPreserves (round3ParameterLiftedPrimaryChart Data ip nu W piece) := by
  apply round3ParameterChartPullback_preserves
  intro z hz
  exact (piece.data.2.2.2.1 z hz).1

theorem round3ParameterLiftedPrimaryChart_target
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × D)
    (hz : z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).target) :
    z.1 ∈ (Data.parameterChart ip).source ∧
    ((Data.parameterChart ip) z.1,z.2) ∈ piece.native.target := by
  have hh := (round3ParameterChartPullback_target (Data.parameterChart ip).symm
    (actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native) z).mp hz
  refine ⟨hh.1,?_⟩
  rw [← piece.data.1]
  exact hh.2.1

theorem round3ParameterLiftedPrimaryChart_active
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × D)
    (hz : z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).target) :
    (z.1,(piece.slices ((Data.parameterChart ip) z.1)).symm z.2) ∈
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := by
  obtain ⟨hp,ht⟩ := round3ParameterLiftedPrimaryChart_target Data ip nu W piece z hz
  have hs := actual_host_slice_source_point _ _ _ _ piece.data
    ((Data.parameterChart ip) z.1,z.2) ht
  have ha := piece.active _ hs
  simpa only [(Data.parameterChart ip).left_inv hp] using ha

theorem round3ParameterLiftedPrimaryChart_inverse
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × D)
    (hz : z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).target) :
    (round3ParameterLiftedPrimaryChart Data ip nu W piece).symm z =
      (z.1,(piece.slices ((Data.parameterChart ip) z.1)).symm z.2) := by
  obtain ⟨hp,ht⟩ := round3ParameterLiftedPrimaryChart_target Data ip nu W piece z hz
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  unfold round3ParameterLiftedPrimaryChart
  rw [round3ParameterChartPullback_symm_apply]
  change ((Data.parameterChart ip).symm
      ((actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native).symm
        ((Data.parameterChart ip) z.1,z.2)).1,
    ((actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native).symm
      ((Data.parameterChart ip) z.1,z.2)).2) = _
  rw [hpair _ ht,(Data.parameterChart ip).left_inv hp]

theorem round3ParameterLiftedPrimaryChart_phase
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × D)
    (hz : z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).target) :
    Data.phase nu (z.1,(piece.slices ((Data.parameterChart ip) z.1)).symm z.2) = z.2 0 := by
  obtain ⟨hp,ht⟩ := round3ParameterLiftedPrimaryChart_target Data ip nu W piece z hz
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  simpa only [(Data.parameterChart ip).left_inv hp] using hphase _ ht

set_option backward.isDefEq.respectTransparency true in
theorem round3ParameterLiftedPrimaryChart_normal
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × D)
    (hz : z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).target) :
    Data.freeNormal nu (z.1,(piece.slices ((Data.parameterChart ip) z.1)).symm z.2) ∈
      normalSpace (I := 𝓙) (fun x => Data.F (z.1,x))
        ((piece.slices ((Data.parameterChart ip) z.1)).symm z.2) := by
  exact hn.normal nu (z.1,(piece.slices ((Data.parameterChart ip) z.1)).symm z.2)
    (round3ParameterLiftedPrimaryChart_active Data ip nu W piece z hz)

set_option backward.isDefEq.respectTransparency true in
def round3ParameterOriginalPrimaryFamily
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    {Β : Type*} [Fintype Β]
    (ip : Fin Data.primaryCount → Β → Fin Data.parameterCount)
    (W : Fin Data.primaryCount → Β → Set (Ep × M))
    (piece : ∀ nu beta, Round3PreparedPrimaryPiece Data (ip nu beta) nu (W nu beta)) :
    Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) (fun p x => Data.F (p,x)) where
  phase := Data.phase
  cutoff := Data.cutoff
  normal := Data.freeNormal
  linearArgument := Data.linearArgument
  eta := fun nu beta z => if z.1 ∈ (Data.parameterChart (ip nu beta)).source then
    (piece nu beta).cutoff ((Data.parameterChart (ip nu beta)) z.1,z.2) else 0
  chart := fun nu beta => round3ParameterLiftedPrimaryChart Data (ip nu beta) nu (W nu beta) (piece nu beta)
  inverse := fun nu beta p x => ((piece nu beta).slices ((Data.parameterChart (ip nu beta)) p)).symm x
  normal_mem := fun nu beta z hz => round3ParameterLiftedPrimaryChart_normal Data hd hs hn
    (ip nu beta) nu (W nu beta) (piece nu beta) z hz

theorem round3ParameterOriginalPrimaryFamily_preserves
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    {Β : Type*} [Fintype Β]
    (ip : Fin Data.primaryCount → Β → Fin Data.parameterCount)
    (W : Fin Data.primaryCount → Β → Set (Ep × M))
    (piece : ∀ nu beta, Round3PreparedPrimaryPiece Data (ip nu beta) nu (W nu beta)) :
    ∀ nu beta, Round3ParameterChartPreserves
      ((round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece).chart nu beta) :=
  fun nu beta => round3ParameterLiftedPrimaryChart_preserves Data (ip nu beta) nu (W nu beta) (piece nu beta)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterOriginalPrimaryFamily
#print axioms GlobalEmbedding.Continuation.round3ParameterLiftedPrimaryChart_phase
#print axioms GlobalEmbedding.Continuation.round3ParameterOriginalPrimaryFamily_preserves
