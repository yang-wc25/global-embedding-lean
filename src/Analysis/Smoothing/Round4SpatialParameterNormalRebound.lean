import Smoothing.Round3OuterParameterCoverProfiles
import Smoothing.Round4SpatialHostNormalProfile

/-! The actual smoothing stage over an arbitrary closed parameter manifold
constructs its one intrinsic normal, all original normal budgets and the true
original normal conditions. Every native and original observer map is supplied
by the same actual cross-parameter charts; quantitative chart input is needed
only on genuine original samples. The named finite host-normal profile precedes the current SF/SH.
No additional normal bound is required; the actual returned rebound uses
the same numeric profile whose raw-prefix dependence has been proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
universe uA
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance hostCoverFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance

theorem round4_parameter_actual_spatial_normal_rebound
    (BS0 TS0 BP0 TP0 T Forward Given : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hT : ∀ j, 0 ≤ T j) (hForward : ∀ j, 0 ≤ Forward j) (hGiven : ∀ j, 0 ≤ Given j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (r : ℕ)
    (budget cF cT mu : ℝ) (hbudget : 0 ≤ budget)
    (hcF : 0 < cF) (hcT : 0 < cT) (hmu : 0 < mu) :
    let C := round4SpatialHostNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
      T Forward Given Ds Dp r budget cF cT mu hmu
    (∀ j, 0 ≤ C j) ∧ ∀
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius r budget reference givenPacket)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hK : Data.parameterSet = univ)
    (domain : Fin Data.primaryCount → Set (P × M))
    (hDomain : ∀ nu, IsOpen (domain nu))
    (hSub : ∀ nu, domain nu ⊆ Data.primaryDomain nu)
    (hCover : ∀ nu, incrementsOriginalRelativeCutoffSupport Data nu ⊆ domain nu),
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference givenPacket stage) p
    let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
      (fun p x => Data.F (p,x)) hF (fun p x => Data.phase nu (p,x)) (Data.freeNormal nu)
    ∀ (A : Fin Data.primaryCount → Type uA)
    (host : ∀ nu, Fin Data.parameterCount → A nu → Fin Data.atlas.count)
    (b : ∀ nu, Fin Data.parameterCount → A nu → OpenPartialHomeomorph X X)
    (e : ∀ nu, Fin Data.parameterCount → A nu → Ep → OpenPartialHomeomorph M D)
    (carrier : ∀ nu, Fin Data.parameterCount → A nu → Set (Ep × M)),
    (∀ nu ip a, ActualOriginalHostSliceData (Data.atlas.chart (host nu ip a)) (b nu ip a)
      (fun w : Ep × M => Data.phase nu ((Data.parameterChart ip).symm w.1,w.2)) (e nu ip a)) →
    (∀ nu ip a, (b nu ip a).source ⊆ actualOriginalNativeOpen Data (host nu ip a,ip)) →
    (∀ nu ip a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)).source →
      ((Data.parameterChart ip).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) →
    (∀ nu ip a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)).source →
      w.2 ∈ Data.atlas.inner (host nu ip a)) →
    (∀ nu ip a, IsOpen (carrier nu ip a)) →
    (∀ nu ip a, carrier nu ip a ⊆ (actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)).source) →
    (∀ nu ip (w : Ep × M), w.1 ∈ (Data.parameterChart ip).target →
      ((Data.parameterChart ip).symm w.1,w.2) ∈ domain nu → ∃ a,
      w ∈ carrier nu ip a) →
    (∀ nu ip a z, z ∈ (b nu ip a).target → ∀ w : D, cF*‖w‖^2 ≤
      ‖fderiv ℝ ((fun x => Data.F ((Data.parameterChart ip).symm z.1,x)) ∘ (e nu ip a z.1).symm) z.2 w‖^2) →
    (∀ nu ip a z, z ∈ (b nu ip a).target → ∀ w : Tdata, cT*‖w‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => Data.F ((Data.parameterChart ip).symm z.1,x))
        (hF ((Data.parameterChart ip).symm z.1)) (e nu ip a z.1).symm z.2 w‖^2) →
    (∀ nu ip a z, z ∈ (b nu ip a).target → mu ≤
      ‖actualOriginalFreeNormalFieldRaw (fun p x => Data.F ((Data.parameterChart ip).symm p,x))
        (fun p => hF ((Data.parameterChart ip).symm p)) (e nu ip a)
        (fun z : X => Data.freeNormal nu ((Data.parameterChart ip).symm z.1,(e nu ip a z.1).symm z.2)) z‖) →
    (∀ j, parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤) →
    (∀ j, (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ Given j) →
    (∀ nu ip a k z, z ∈ (b nu ip a).target ∩
      (actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)).symm ⁻¹' carrier nu ip a →
      parameterTensorModelEquiv (m+1) d ((b nu ip a).symm z) ∈
        incrementsOriginalEvaluation Data.atlas Data.parameterChart
          Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (host nu ip a,ip) →
      ‖iteratedFDeriv ℝ k (b nu ip a).symm z‖ ≤ T k) →
    (∀ nu (i : Fin Data.atlas.count × Fin Data.parameterCount) a k y,
      y ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i ∩
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart i ∩
        (round3OriginalNativeObserverPoint Data i) ⁻¹' carrier nu i.2 a) →
      ‖iteratedFDeriv ℝ k (b nu i.2 a)
        ((actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart (host nu i.2 a)))
          (round3OriginalNativeObserverPoint Data i y))‖ ≤ Forward k) →
    Nonempty (Round3RepairNormalRebound stage normal domain C) := by
  let C := round4SpatialHostNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    T Forward Given Ds Dp r budget cF cT mu hmu
  obtain ⟨hC,hMake⟩ := round4_actual_spatial_normal_rebound_stage
    (m := m) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 T (round3HostObserverProfile m d Forward Given)
    (round3HostReferenceProfile m d N T Given)
    hBS0 hTS0 hBP0 hTP0 hT (round3HostObserverProfile_nonneg m d Forward Given hForward hGiven)
    (round3HostReferenceProfile_nonneg m d N T Given hT hGiven)
    Ds Dp radius hradius r budget cF cT mu hbudget hcF hcT hmu
  refine ⟨hC,?_⟩
  intro Data reference givenPacket stage hd hs hK domain hDomain hSub hCover hF normal
    A host b e carrier hData hNative hActive hInner hCarrierOpen hCarrierSub hCoverActual hFirst hFrame hReserve hFixed hFixedBound hInv hForw
  let cover := fun nu => round3ParameterHostNormalCover Data hd hs hF nu (domain nu)
    (host nu) (b nu) (e nu) (hData nu) (hNative nu) (hActive nu) (hInner nu) (carrier nu) (hCarrierOpen nu) (hCarrierSub nu) (hCoverActual nu)
    cF cT mu (hFirst nu) (hFrame nu) (hReserve nu)
  have hProfiles (nu : Fin Data.primaryCount) := round3_parameter_host_normal_cover_fixed_profiles
    Data hd hs hF nu (domain nu) (host nu) (b nu) (e nu)
    (hData nu) (hNative nu) (hActive nu) (hInner nu) (carrier nu) (hCarrierOpen nu) (hCarrierSub nu) (hCoverActual nu) cF cT mu
    (hFirst nu) (hFrame nu) (hReserve nu) T Forward Given hT hForward hFixed hFixedBound
    (hInv nu) (hForw nu)
  apply hMake Data reference givenPacket stage hK hd domain hDomain hSub hCover Data.freeNormal A cover
  · exact round3_repair_normal_physical_cover_of_closed_parameters Data hd hK hF normal
      Data.freeNormal domain A cF cT mu cover
  · exact fun nu => (hProfiles nu).1
  · exact fun nu => (hProfiles nu).2.1
  · exact fun nu => (hProfiles nu).2.2
  · exact hs.phase_joint
  · exact hs.cutoff_joint

#print axioms round4_parameter_actual_spatial_normal_rebound
end GlobalEmbedding.Continuation
