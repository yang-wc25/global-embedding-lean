import NormalPolar.JointSecondarySignedCarrierGood
import Probes.ActualOriginalSignedPhaseGood
import Smoothing.ParameterRound2OriginalFiniteReserveGerm
import GlobalEmbedding.Paper.IncrementsOriginalImmersionInputs

/-! The exact original ordered signed phases supply actual secondary seeds.
Goodness, closed carriers, smooth phases and open primary domains are derived
from the unchanged original native Data. The chosen original spatial slice
is fixed before all contractions and derivative scales; this is a geometric
seed construction, never a derivative of a selected parameter witness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

def jointSecondaryOriginalSignedPhase
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (p : P)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) : M → ℝ :=
  fun x => ![Data.phase r.val.1.1 (p,x)+Data.phase r.val.1.2 (p,x),
    Data.phase r.val.1.1 (p,x)-Data.phase r.val.1.2 (p,x),
    -Data.phase r.val.1.1 (p,x)+Data.phase r.val.1.2 (p,x),
    -Data.phase r.val.1.1 (p,x)-Data.phase r.val.1.2 (p,x)] r.val.2

def jointSecondaryOriginalSignedCarrier
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (p : P)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) : Set M :=
  (fun x => (p,x)) ⁻¹' (incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
    incrementsOriginalRelativeCutoffSupport Data r.val.1.2)

def jointSecondaryOriginalSignedDomain
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (p : P)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) : Set M :=
  (fun x => (p,x)) ⁻¹' (Data.primaryDomain r.val.1.1 ∩ Data.primaryDomain r.val.1.2)

theorem jointSecondaryOriginalSignedCarrier_closed
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (p : P) (hp : p ∈ Data.parameterOpen)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) :
    IsClosed (jointSecondaryOriginalSignedCarrier Data p r) := by
  have heq : jointSecondaryOriginalSignedCarrier Data p r =
      (fun x : M => (p,x)) ⁻¹' (tsupport (Data.cutoff r.val.1.1) ∩
        tsupport (Data.cutoff r.val.1.2)) := by
    ext x
    simp only [jointSecondaryOriginalSignedCarrier,mem_preimage,mem_inter_iff,
      parameterRound2_original_relativeSupport_eq Data hd.parameter_open,
      incrementsOriginalParameterRegion,mem_prod,hp,mem_univ,true_and]
  rw [heq]
  exact ((isClosed_tsupport _).inter (isClosed_tsupport _)).preimage
    (continuous_const.prodMk continuous_id)

theorem jointSecondaryOriginalSignedDomain_open
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (p : P)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) :
    IsOpen (jointSecondaryOriginalSignedDomain Data p r) :=
  ((hd.primary_open r.val.1.1).inter (hd.primary_open r.val.1.2)).preimage
    (continuous_const.prodMk continuous_id)

theorem jointSecondaryOriginalSignedCarrier_domain
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (p : P)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) :
    jointSecondaryOriginalSignedCarrier Data p r ⊆ jointSecondaryOriginalSignedDomain Data p r :=
  fun _ hx => ⟨hd.cutoff_support_local r.val.1.1 hx.1,hd.cutoff_support_local r.val.1.2 hx.2⟩

theorem jointSecondaryOriginalSignedPhase_smooth
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hs : IncrementsOriginalSmoothInputs Data) (p : P) (hp : p ∈ Data.parameterOpen)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) :
    ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ (jointSecondaryOriginalSignedPhase Data p r)
      (jointSecondaryOriginalSignedDomain Data p r) := by
  let O := jointSecondaryOriginalSignedDomain Data p r
  have hn : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ (fun x => Data.phase r.val.1.1 (p,x)) O :=
    (hs.phase_joint r.val.1.1).comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun x hx => ⟨hx.1,hp,mem_univ _⟩)
  have hm : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ (fun x => Data.phase r.val.1.2 (p,x)) O :=
    (hs.phase_joint r.val.1.2).comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun x hx => ⟨hx.2,hp,mem_univ _⟩)
  have hAll (q : Fin 4) : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞
      (fun x => ![Data.phase r.val.1.1 (p,x)+Data.phase r.val.1.2 (p,x),
        Data.phase r.val.1.1 (p,x)-Data.phase r.val.1.2 (p,x),
        -Data.phase r.val.1.1 (p,x)+Data.phase r.val.1.2 (p,x),
        -Data.phase r.val.1.1 (p,x)-Data.phase r.val.1.2 (p,x)] q) O := by
    fin_cases q
    · exact hn.add hm
    · exact hn.sub hm
    · exact hn.neg.add hm
    · exact hn.neg.sub hm
  exact hAll r.val.2

/-- No signed Good hypothesis or adapted/raw profile is supplied: the exact
original qualitative conditions construct them on the original support pair. -/
theorem jointSecondary_original_signed_seed
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (p : P) (hpO : p ∈ Data.parameterOpen)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) :
    let F := fun x => Data.F (p,x)
    let hF := incrementsOriginal_slice_contMDiff Data hd hs p hpO
    let phase := jointSecondaryOriginalSignedPhase Data p r
    let K := jointSecondaryOriginalSignedCarrier Data p r
    ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧ U ⊆ jointSecondaryOriginalSignedDomain Data p r ∧
      Nonempty (JointSecondarySignedSeed (Ep := Ep) F hF phase K U) := by
  intro F hF phase K
  apply jointSecondary_exists_signed_seed_of_carrier_good F hF (hImm.immersion p hpO)
    phase K (jointSecondaryOriginalSignedDomain Data p r)
    (jointSecondaryOriginalSignedCarrier_closed Data hd p hpO r)
    (jointSecondaryOriginalSignedDomain_open Data hd p r)
    (jointSecondaryOriginalSignedCarrier_domain Data hd p r)
    (jointSecondaryOriginalSignedPhase_smooth Data hs p hpO r)
  intro x hx
  exact actual_original_signed_secondary_phase_good Data hd hs hp r (p,x) hx

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondaryOriginalSignedCarrier_closed
#print axioms GlobalEmbedding.Continuation.jointSecondaryOriginalSignedPhase_smooth
#print axioms GlobalEmbedding.Continuation.jointSecondary_original_signed_seed
