import NormalPolar.JointSecondaryOriginalSignedSeed
import NormalPolar.JointSecondaryWeightedPhaseCovectors
import Upgrade.ProbeInterface

/-! The actual original primary phase at the fixed reference slice retains
its open smoothness domain and its distinct closed cutoff carrier. This is
the original background component of the full mixed signed seed family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade
open Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

def jointSecondaryOriginalPrimaryCarrier
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (p : P)
    (l : Fin Data.primaryCount) : Set M :=
  (fun x => (p,x)) ⁻¹' incrementsOriginalRelativeCutoffSupport Data l

def jointSecondaryOriginalPrimaryDomain
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (p : P)
    (l : Fin Data.primaryCount) : Set M :=
  (fun x => (p,x)) ⁻¹' Data.primaryDomain l

theorem jointSecondaryOriginalPrimaryCarrier_closed
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (p : P) (hp : p ∈ Data.parameterOpen)
    (l : Fin Data.primaryCount) : IsClosed (jointSecondaryOriginalPrimaryCarrier Data p l) := by
  have heq : jointSecondaryOriginalPrimaryCarrier Data p l =
      (fun x : M => (p,x)) ⁻¹' tsupport (Data.cutoff l) := by
    ext x
    simp only [jointSecondaryOriginalPrimaryCarrier,mem_preimage,
      parameterRound2_original_relativeSupport_eq Data hd.parameter_open,
      incrementsOriginalParameterRegion,mem_inter_iff,mem_prod,hp,mem_univ,true_and]
  rw [heq]
  exact (isClosed_tsupport _).preimage (continuous_const.prodMk continuous_id)

theorem jointSecondaryOriginalPrimaryDomain_open
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (p : P) (l : Fin Data.primaryCount) :
    IsOpen (jointSecondaryOriginalPrimaryDomain Data p l) :=
  (hd.primary_open l).preimage (continuous_const.prodMk continuous_id)

theorem jointSecondaryOriginalPrimaryCarrier_domain
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (p : P) (l : Fin Data.primaryCount) :
    jointSecondaryOriginalPrimaryCarrier Data p l ⊆ jointSecondaryOriginalPrimaryDomain Data p l :=
  fun _ hx => hd.cutoff_support_local l hx

theorem jointSecondaryOriginalPrimaryPhase_smooth
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hs : IncrementsOriginalSmoothInputs Data) (p : P) (hp : p ∈ Data.parameterOpen)
    (l : Fin Data.primaryCount) :
    ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ (fun x => Data.phase l (p,x))
      (jointSecondaryOriginalPrimaryDomain Data p l) :=
  (hs.phase_joint l).comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
    (fun _ hx => ⟨hx,hp,mem_univ _⟩)

theorem jointSecondaryOriginalPrimaryPhase_covector
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (p : P) (l : Fin Data.primaryCount) (x : M) :
    jointSecondaryPhaseCovector (m := m) (fun y => Data.phase l (p,y)) x =
      incrementsOriginalPhaseCovector Data l p x := rfl

theorem jointSecondaryOriginalPrimaryPhase_good
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (p : P) (hpO : p ∈ Data.parameterOpen) (l : Fin Data.primaryCount)
    (x : M) (hx : x ∈ jointSecondaryOriginalPrimaryCarrier Data p l) :
    GoodCovector (fun y => Data.F (p,y)) (incrementsOriginal_slice_contMDiff Data hd hs p hpO)
      x (mfderiv IM 𝓘(ℝ,ℝ) (fun y => Data.phase l (p,y)) x) := by
  have hg := hp.primary_good l (p,x) ⟨hd.cutoff_support_local l hx,hpO,mem_univ _⟩
  exact hg

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondaryOriginalPrimaryCarrier_closed
#print axioms GlobalEmbedding.Continuation.jointSecondaryOriginalPrimaryPhase_good
