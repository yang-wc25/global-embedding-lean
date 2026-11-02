import Probes.Round3ParameterPreparedPrimaryLift
import Probes.ActualIncrementOriginalPhysicalGeometry
import Probes.ActualIncrementGoodPhaseGeometry

/-! The original Good phase and original free normal prove the actual
transverse Gram and normal-kernel identities on a lifted physical chart.
These are pointwise identities for the real sliced map and are invariant
under changing only the parameter coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
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

theorem round3ParameterLiftedPrimaryChart_slice_target
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × D)
    (hz : z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).target) :
    z.2 ∈ (piece.slices ((Data.parameterChart ip) z.1)).target := by
  obtain ⟨hp,ht⟩ := round3ParameterLiftedPrimaryChart_target Data ip nu W piece z hz
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  rw [het]
  exact ht

theorem round3ParameterLiftedPrimaryChart_target_of_slice
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × D)
    (hp : z.1 ∈ (Data.parameterChart ip).source)
    (hx : z.2 ∈ (piece.slices ((Data.parameterChart ip) z.1)).target) :
    z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).target := by
  apply (round3ParameterChartPullback_target_iff (Data.parameterChart ip).symm
    (actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native)
    (fun y hy => (piece.data.2.2.2.1 y hy).1) z hp).mpr
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  rw [hat]
  rwa [het] at hx

theorem round3ParameterLiftedPrimaryChart_forward_phase
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × M)
    (hz : z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).source) :
    Data.phase nu z = (round3ParameterLiftedPrimaryChart Data ip nu W piece z).2 0 := by
  obtain ⟨hp,ha,hh⟩ := (round3ParameterChartPullback_source (Data.parameterChart ip).symm
    (actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native) z).mp hz
  have he := (piece.data.2.2.2.1 ((Data.parameterChart ip) z.1,z.2) ha).2
  simpa only [round3ParameterLiftedPrimaryChart,round3ParameterChartPullback_apply,
    OpenPartialHomeomorph.symm_symm,(Data.parameterChart ip).left_inv hp] using he.symm

theorem round3ParameterLiftedPrimaryChart_gram
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hPhase : IncrementsOriginalPhaseConditions Data hd hs)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)))
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × D)
    (hz : z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).target) :
    let e := piece.slices ((Data.parameterChart ip) z.1)
    let b := incrementsTransversePairing (fun x => Data.F (z.1,x)) (hF z.1) (e.symm z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections e.symm z.2 a.succ)
    (b.comp b.adjoint).IsInvertible := by
  intro e b
  have hp := (round3ParameterLiftedPrimaryChart_target Data ip nu W piece z hz).1
  have hx := round3ParameterLiftedPrimaryChart_slice_target Data ip nu W piece z hz
  have hActive := round3ParameterLiftedPrimaryChart_active Data ip nu W piece z hz
  have hPhaseCoord (x : D) (hxt : x ∈ e.target) : Data.phase nu (z.1,e.symm x) = x 0 :=
    round3ParameterLiftedPrimaryChart_phase Data ip nu W piece (z.1,x)
      (round3ParameterLiftedPrimaryChart_target_of_slice Data ip nu W piece (z.1,x) hp hxt)
  have hopen : IsOpen (Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :=
    (hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ)
  have hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (fun y => Data.phase nu (z.1,y)) (e.symm z.2) :=
    (((hs.phase_joint nu).contMDiffAt (hopen.mem_nhds hActive)).comp (e.symm z.2)
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  exact actual_increment_transverse_gram_of_good_phase (fun x => Data.F (z.1,x)) (hF z.1)
    (fun x => Data.phase nu (z.1,x)) e (piece.data.2.2.2.2.1 _)
    e.target e.open_target subset_rfl z.2 hx hpsi hPhaseCoord
    (hPhase.primary_good nu (z.1,e.symm z.2) hActive)

theorem round3ParameterLiftedPrimaryChart_normal_kernel
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)))
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × D)
    (hz : z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).target) :
    let e := piece.slices ((Data.parameterChart ip) z.1)
    incrementsTransversePairing (fun x => Data.F (z.1,x)) (hF z.1) (e.symm z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections e.symm z.2 a.succ)
      ⟨Data.freeNormal nu (z.1,e.symm z.2),round3ParameterLiftedPrimaryChart_normal Data hd hs hn ip nu W piece z hz⟩ = 0 := by
  intro e
  have hp := (round3ParameterLiftedPrimaryChart_target Data ip nu W piece z hz).1
  have hx := round3ParameterLiftedPrimaryChart_slice_target Data ip nu W piece z hz
  have hActive := round3ParameterLiftedPrimaryChart_active Data ip nu W piece z hz
  have hmap (x : D) (hxt : x ∈ e.target) : (z.1,e.symm x) ∈ Data.primaryDomain nu :=
    (round3ParameterLiftedPrimaryChart_active Data ip nu W piece (z.1,x)
      (round3ParameterLiftedPrimaryChart_target_of_slice Data ip nu W piece (z.1,x) hp hxt)).1
  have hAdapt (x : D) (hxt : x ∈ e.target) : Data.phase nu (z.1,e.symm x) = x 0 :=
    round3ParameterLiftedPrimaryChart_phase Data ip nu W piece (z.1,x)
      (round3ParameterLiftedPrimaryChart_target_of_slice Data ip nu W piece (z.1,x) hp hxt)
  exact actual_original_free_normal_transverse_kernel Data hd hs hn nu z.1 hActive.2.1
    e (piece.data.2.2.2.2.1 _) e.target e.open_target subset_rfl hmap hAdapt z.2 hx

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterLiftedPrimaryChart_gram
#print axioms GlobalEmbedding.Continuation.round3ParameterLiftedPrimaryChart_normal_kernel
