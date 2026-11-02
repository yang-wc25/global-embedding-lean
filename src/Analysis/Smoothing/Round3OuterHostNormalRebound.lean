import Smoothing.Round3OuterHostCoverProfiles
import Smoothing.Round3RepairNormalCoverConsumer

/-! Actual same-SF normal rebound with every derivative profile and the
physical cover produced internally. Fixed reference charts and their stable
reserves are the only geometric input. Constants precede the current stage. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
universe uA
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
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

theorem round3_exists_uniform_actual_host_normal_rebound
    (BS0 TS0 BP0 TP0 T Forward Given : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hT : ∀ j, 0 ≤ T j) (hForward : ∀ j, 0 ≤ Forward j) (hGiven : ∀ j, 0 ≤ Given j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (r : ℕ)
    (budget cF cT mu : ℝ) (hbudget : 0 ≤ budget)
    (hcF : 0 < cF) (hcT : 0 < cT) (hmu : 0 < mu) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius r budget reference givenPacket)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hId : ∀ ip, Data.parameterChart ip = OpenPartialHomeomorph.refl Ep)
    (ip : Fin Data.parameterCount)
    (domain : Fin Data.primaryCount → Set (Ep × M))
    (hDomain : ∀ nu, IsOpen (domain nu))
    (hSub : ∀ nu, domain nu ⊆ Data.primaryDomain nu)
    (hCover : ∀ nu, incrementsOriginalRelativeCutoffSupport Data nu ⊆ domain nu),
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference givenPacket stage) p
    let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
      (fun p x => Data.F (p,x)) hF (fun p x => Data.phase nu (p,x)) (Data.freeNormal nu)
    ∀ (A : Fin Data.primaryCount → Type uA)
    (host : ∀ nu, A nu → Fin Data.atlas.count)
    (b : ∀ nu, A nu → OpenPartialHomeomorph X X)
    (e : ∀ nu, A nu → Ep → OpenPartialHomeomorph M D),
    (∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (host nu a)) (b nu a)
      (Data.phase nu) (e nu a)) →
    (∀ nu a, (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) →
    (∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source →
      w.2 ∈ Data.atlas.inner (host nu a)) →
    (∀ nu w, w ∈ domain nu → ∃ a,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source) →
    (∀ nu a z, z ∈ (b nu a).target → ∀ w : D, cF*‖w‖^2 ≤
      ‖fderiv ℝ ((fun x => Data.F (z.1,x)) ∘ (e nu a z.1).symm) z.2 w‖^2) →
    (∀ nu a z, z ∈ (b nu a).target → ∀ w : Tdata, cT*‖w‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => Data.F (z.1,x)) (hF z.1)
        (e nu a z.1).symm z.2 w‖^2) →
    (∀ nu a z, z ∈ (b nu a).target → mu ≤
      ‖actualOriginalFreeNormalFieldRaw (fun p x => Data.F (p,x)) hF (e nu a)
        (fun z : X => Data.freeNormal nu (z.1,(e nu a z.1).symm z.2)) z‖) →
    (∀ j, parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤) →
    (∀ j, (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ Given j) →
    (∀ nu a k z, z ∈ (b nu a).target → ‖iteratedFDeriv ℝ k (b nu a).symm z‖ ≤ T k) →
    (∀ nu a k z, z ∈ (b nu a).source → ‖iteratedFDeriv ℝ k (b nu a) z‖ ≤ Forward k) →
    Nonempty (Round3RepairNormalRebound stage normal domain C) := by
  obtain ⟨C,hC,hMake⟩ := round3_exists_uniform_actual_normal_rebound_stage
    (m := m) (d := d) (N := N) (M := M) (P := Ep)
    BS0 TS0 BP0 TP0 T (round3HostObserverProfile m d Forward Given)
    (round3HostReferenceProfile m d N T Given)
    hBS0 hTS0 hBP0 hTP0 hT (round3HostObserverProfile_nonneg m d Forward Given hForward hGiven)
    (round3HostReferenceProfile_nonneg m d N T Given hT hGiven)
    Ds Dp radius hradius r budget cF cT mu hbudget hcF hcT hmu
  refine ⟨C,hC,?_⟩
  intro Data reference givenPacket stage hd hs hId ip domain hDomain hSub hCover hF normal
    A host b e hData hActive hInner hCoverActual hFirst hFrame hReserve hFixed hFixedBound hInv hForw
  let cover := fun nu => round3HostNormalCover Data hd hs hId hF nu (domain nu)
    (host nu) (b nu) (e nu) (hData nu) (hActive nu) (hInner nu) (hCoverActual nu)
    cF cT mu (hFirst nu) (hFrame nu) (hReserve nu)
  have hProfiles (nu : Fin Data.primaryCount) := round3_actual_host_normal_cover_fixed_profiles
    Data hd hs hId hF nu (domain nu) (host nu) (b nu) (e nu)
    (hData nu) (hActive nu) (hInner nu) (hCoverActual nu) cF cT mu
    (hFirst nu) (hFrame nu) (hReserve nu) T Forward Given hT hForward hFixed hFixedBound
    (hInv nu) (hForw nu)
  apply hMake Data reference givenPacket stage hd domain hDomain hSub hCover Data.freeNormal A cover
  · intro nu z hz
    exact round3_actual_host_physical_cover Data hId ip (domain nu) (host nu) (b nu)
      (hCoverActual nu) z hz.1
  · exact fun nu => (hProfiles nu).1
  · exact fun nu => (hProfiles nu).2.1
  · exact fun nu => (hProfiles nu).2.2
  · exact hs.phase_joint
  · exact hs.cutoff_joint

#print axioms round3_exists_uniform_actual_host_normal_rebound
end GlobalEmbedding.Continuation
