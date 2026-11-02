import OriginalIncrements.CountedLowPrimaryRefinement
import OriginalIncrements.OriginalFinitePrimarySupply
import Repair.FullIncrementNovOpenPrimaryPieces

/-!
# The actual primary packet retains total per-owner piece bounds

Every packet is the same one used by the explicit native/observer/grid
certificates. Its model radius, centers, and total finite cardinal bound
are preserved from the counted primitive. No original estimate for a
future constructed packet is assumed.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
open OriginalCollars
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

variable [T2Space M]

/-- The actual budgeted packet together with total per-owner cardinality.
The stored radius and numerical budget precede every later q, scale and
observation order. The bound is not a maximum of actual cardinalities. -/
structure OriginalCountedPrimarySupply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    extends OriginalBudgetedPrimarySupply Data theta where
  radius : Fin Data.primaryCount → (Fin Data.atlas.count × Fin Data.parameterCount) → ℝ
  radius_pos : ∀ nu i, 0 < radius nu i
  centers : ∀ nu i, (↑(packet.s nu i) : Set X) ⊆ Metric.closedBall 0 (radius nu i)
  center_active : ∀ nu i (a : packet.s nu i),
    ((Data.parameterChart i.2).symm a.val.1,(Data.atlas.chart i.1).symm a.val.2) ∈
      tsupport (theta i) ∩ incrementsOriginalRelativeCutoffSupport Data nu
  total_card : ∀ nu i, (packet.s nu i).card ≤
    originalPhaseTotalPieceBudget («Ep» := Ep) (m := m) (mu nu i) (Mb nu i)
      (radius nu i) (buffer nu i) (mu_pos nu i) (Mb_nonneg nu i) (buffer_pos nu i)


theorem original_counted_primary_pieces_from_low_phase_budget
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hParam : ∀ w ∈ W, w.1 ∈ (Data.parameterChart i.2).target)
    (hOriginal : MapsTo (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2))
      W (incrementsOriginalParameterRegion Data))
    (theta : Ep × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hTheta : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta)
    (hThetaSupport : tsupport theta ⊆ W ∩
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source)
    (ell : ℝ) (hell : 0 < ell) (Packet : ℕ → ℝ)
    (hLow : ∀ k, k ≤ 1 → ∀ w : Ep × M, w ∈ tsupport theta →
      w ∈ incrementsGlobalRelativeSupport W
        (fun z => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)) →
      ell^k*‖iteratedFDeriv ℝ (k+1) (originalNativePrimaryPhase Data nu i)
        (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1) w)‖ ≤
        actualOriginalTotalPhaseJetCost (m+1) d k*Packet k+1) :
    ∃ (mu Mb R buffer : ℝ) (s : Finset X) (out : s → Round3PreparedPrimaryPiece Data i.2 nu W),
      ∃ (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer),
      0 < R ∧
      s.card ≤ originalPhaseTotalPieceBudget («Ep» := Ep) (m := m) mu Mb R buffer hmu hMb hbuffer ∧
      (↑s : Set X) ⊆ Metric.closedBall 0 R ∧
      (∀ a : s, (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm a.val ∈
        tsupport theta ∩ incrementsGlobalRelativeSupport W
          (fun z => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2))) ∧
      (∀ a : s, (out a).host = i.1) ∧
      (∀ a : s, tsupport (out a).cutoff ⊆ tsupport theta) ∧
      (∀ y ∈ incrementsGlobalRelativeSupport W
          (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)),
        ∀ᶠ w in 𝓝 y, ∑ a : s, (out a).cutoff w = theta w) ∧
      (∀ y, (Finset.univ.filter (fun a : s => y ∈ tsupport (out a).cutoff)).card ≤ 5^Module.finrank ℝ X) ∧
      (∀ a : s, ∀ x ∈ (out a).native.source,
        ‖fderiv ℝ (out a).native x‖ ≤ 2*(1+2*Mb)) ∧
      (∀ (a : s) k, 1 ≤ k → ∀ x ∈ (out a).native.source,
        ‖iteratedFDeriv ℝ (k+1) (out a).native x‖ ≤
          2^(k+2)*‖iteratedFDeriv ℝ (k+1)
            ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘
              (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) x‖) ∧
      (∀ (a : s) (S : Set X), S ⊆ (out a).native.target → ∀ (j : ℕ) (weight Mj : ℝ),
        0 < weight → 0 ≤ Mj →
        (∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ (out a).native.symm '' S,
          weight^k*‖iteratedFDeriv ℝ (k+1)
            ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘
              (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) x‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ S,
          weight^(k-1)*‖iteratedFDeriv ℝ k (out a).native.symm y‖ ≤
            actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j) ∧
      (∀ a : s, OriginalRefinementObserverBudgets Data i nu mu Mb (out a).native) ∧
      (∀ a : s, (out a).cutoff = actualHostRefinementCutoff
        (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) theta
        (actualRefinementCutoff X s (buffer/actualPhaseRefinementFactor mu Mb) a.val)) ∧
      (∀ (j : ℕ) (weight : ℝ), 0 ≤ weight → weight ≤ buffer → ∀ (a : s) (x : X),
        weight^j*‖iteratedFDeriv ℝ j
          (actualRefinementCutoff X s (buffer/actualPhaseRefinementFactor mu Mb) a.val) x‖ ≤
          (actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost X j) ∧
      Mb = originalLowPhaseBudget m d Packet ∧ buffer ≤ ell := by
  obtain ⟨mu,Mb,R,buffer,s,b,e,eta,Bnative,hmu,hMb,hbuffer,hR,hcard,hcenters,hCentersActive,hB,hBpos,
    hData,hOpen,hWsource,hActive,hCompactEta,hSmoothEta,hSupportEta,hPartition,hGerm,
    hCount,hNative,hCutoffEq,hCutoffJets,hHigher,hInverse,hMbEq,hBufferLe⟩ :=
    original_counted_low_budget_primary_refinement
      Data hd hs hp i nu W hW hParam hOriginal theta hCompact hTheta hThetaSupport ell hell Packet hLow
  have hObserver (a : s) : OriginalRefinementObserverBudgets Data i nu mu Mb (b a) :=
    original_refinement_observer_budgets_of_actual_jets Data hd hs i nu mu Mb hmu hMb
      (b a) (e a) (hData a) (by simpa only [hB] using hNative a)
      (hHigher a) (hInverse a)
  let out := fun a : s => ({
    host := i.1
    native := b a
    slices := e a
    cutoff := eta a
    data := hData a
    native_source := hOpen a
    source_domain := hWsource a
    active := hActive a
    compact := hCompactEta a
    smooth := hSmoothEta a
    support := fun _ hz => (hSupportEta a hz).1
    Bnative := Bnative
    positive := hBpos
    native_first := hNative a } : Round3PreparedPrimaryPiece Data i.2 nu W)
  exact ⟨mu,Mb,R,buffer,s,out,hmu,hMb,hbuffer,hR,hcard,hcenters,hCentersActive,fun _ => rfl,
    fun a _ hz => (hSupportEta a hz).2,hGerm,hCount,
    (fun a => by simpa only [hB] using hNative a),hHigher,hInverse,hObserver,hCutoffEq,hCutoffJets,hMbEq,hBufferLe⟩

theorem original_open_counted_primary_supply_from_finite_low_phase_budget
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1)
    (ell : ℝ) (hell : 0 < ell) (Packet : ℕ → ℝ)
    (hLow : ∀ (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
      (k : ℕ), k ≤ 1 → ∀ z : P × M, z ∈ tsupport (theta i) →
      z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
      originalPhaseJetAtPhysical Data nu i k ell z <
        actualOriginalTotalPhaseJetCost (m+1) d k*Packet k+1) :
    ∃ supply : OriginalCountedPrimarySupply Data theta,
      (∀ nu i, supply.Mb nu i = originalLowPhaseBudget m d Packet) ∧
      ∀ nu i, supply.buffer nu i ≤ ell := by
  let W := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    ((Data.parameterChart i.2).target ∩ (Data.parameterChart i.2).symm ⁻¹' Data.parameterOpen) ×ˢ
      (univ : Set M)
  let U := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  have hW (i : Fin Data.atlas.count × Fin Data.parameterCount) : IsOpen (W i) :=
    ((Data.parameterChart i.2).symm.continuousOn.isOpen_inter_preimage
      (Data.parameterChart i.2).open_target hd.parameter_open).prod isOpen_univ
  have hSupport' (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M) :=
    fun z hz => ⟨(hSupport i hz).1.1,mem_univ _⟩
  have hLocal (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : P × M)
      (hz : z ∈ tsupport (theta i)) : ((Data.parameterChart i.2) z.1,z.2) ∈ W i := by
    have hs := hSupport i hz
    refine ⟨⟨(Data.parameterChart i.2).map_source hs.1.1,?_⟩,mem_univ _⟩
    change (Data.parameterChart i.2).symm ((Data.parameterChart i.2) z.1) ∈ Data.parameterOpen
    rw [(Data.parameterChart i.2).left_inv hs.1.1]
    exact hs.1.2
  have hNative (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    round3Parameter_native_compact_parent (Data.parameterChart i.2)
      (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i) (hSupport' i)
  have hNSupport (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆
        W i ∩ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := (hNative i).2.2 hy
    exact ⟨hLocal i z hz,mem_univ _,Data.atlas.inner_subset i.1 (hSupport i hz).2⟩
  have hNativeLow (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
      (k : ℕ) (hk : k ≤ 1) (w : Ep × M)
      (hw : w ∈ tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)))
      (hcutoff : w ∈ incrementsGlobalRelativeSupport (W i)
        (fun z => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2))) :
      ell^k*‖iteratedFDeriv ℝ (k+1) (originalNativePrimaryPhase Data nu i)
        (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1) w)‖ ≤
        actualOriginalTotalPhaseJetCost (m+1) d k*Packet k+1 := by
    let pull : Ep × M → P × M := fun z => ((Data.parameterChart i.2).symm z.1,z.2)
    have hPull : ContinuousOn pull (W i) :=
      ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn
        (fun _ hz => hz.1.1)).prodMk continuous_snd.continuousOn
    have hPullSupport := actual_relative_support_pullback_subset (W i)
      (incrementsOriginalParameterRegion Data) pull hPull
      (fun z hz => ⟨hz.1.2,mem_univ _⟩) (Data.cutoff nu) hcutoff
    obtain ⟨z,hz,rfl⟩ := (hNative i).2.2 hw
    have hp : pull ((Data.parameterChart i.2) z.1,z.2) = z := by
      change ((Data.parameterChart i.2).symm ((Data.parameterChart i.2) z.1),z.2) = z
      rw [(Data.parameterChart i.2).left_inv (hSupport i hz).1.1]
    change pull ((Data.parameterChart i.2) z.1,z.2) ∈ incrementsOriginalRelativeCutoffSupport Data nu at hPullSupport
    rw [hp] at hPullSupport
    exact (hLow nu i k hk z hz hPullSupport).le
  have hPieces (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    original_counted_primary_pieces_from_low_phase_budget Data hd hs hp i nu (W i) (hW i)
      (fun _ hy => hy.1.1) (fun z hz => ⟨hz.1.2,mem_univ _⟩)
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      (hNative i).2.1 (hNative i).1 (hNSupport i) ell hell Packet (hNativeLow nu i)
  choose mu Mb R buffer s piece hmu hMb hbuffer hR hcard hcenters hCentersActive hHost hParent hGerm hCount hFirst hHigher hInverse hObserver hCutoffEq hCutoffJets hMbEq hBufferLe using hPieces
  have hCenterPhysical (nu : Fin Data.primaryCount)
      (i : Fin Data.atlas.count × Fin Data.parameterCount) (a : s nu i) :
      ((Data.parameterChart i.2).symm a.val.1,(Data.atlas.chart i.1).symm a.val.2) ∈
        tsupport (theta i) ∩ incrementsOriginalRelativeCutoffSupport Data nu := by
    let w := (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm a.val
    let pull : Ep × M → P × M := fun z => ((Data.parameterChart i.2).symm z.1,z.2)
    have h := hCentersActive nu i a
    have hPull : ContinuousOn pull (W i) :=
      ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn
        (fun _ hz => hz.1.1)).prodMk continuous_snd.continuousOn
    have hOriginal := actual_relative_support_pullback_subset (W i)
      (incrementsOriginalParameterRegion Data) pull hPull
      (fun z hz => ⟨hz.1.2,mem_univ _⟩) (Data.cutoff nu) h.2
    obtain ⟨z,hz,heq⟩ := (hNative i).2.2 h.1
    have hPoint : pull w = z := by
      change pull ((actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm a.val) = z
      rw [← heq]
      change ((Data.parameterChart i.2).symm ((Data.parameterChart i.2) z.1),z.2) = z
      rw [(Data.parameterChart i.2).left_inv (hSupport i hz).1.1]
    change pull w ∈ tsupport (theta i) ∩ incrementsOriginalRelativeCutoffSupport Data nu
    exact ⟨hPoint.symm ▸ hz,hOriginal⟩
  let out := fun nu i (a : s nu i) => fullIncrementNovPrimaryPieceEnlarge Data i.2 nu (W i) (U i)
    (piece nu i a) (fun _ hz => ⟨hz.1.1,hz.2⟩)
  have hLift (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) (a : s nu i) :=
    round3Parameter_original_primary_cutoff Data hd i.2 nu (U i) (out nu i a)
      (theta i) (hCompact i) (hSupport' i) (hNative i).2.2 (hParent nu i a)
  let packet : Round3ParameterWholePrimaryPieceSupply Data theta := {
    s := s
    piece := out
    host := hHost
    native_parent := hParent
    smooth := fun nu i a => (hLift nu i a).1
    compact := fun nu i a => (hLift nu i a).2.1
    parent := fun nu i a => (hLift nu i a).2.2.1
    source := fun nu i a => (hLift nu i a).2.2.2
    partition := fun nu i z hz => fullIncrementNov_local_primary_partition_transport Data i.2 nu
      (U i) (W i) (hW i) (out nu i) (theta i) (hSupport' i) (hLocal i)
      (fun a => (hLift nu i a).2.2.1) (hGerm nu i) z hz
    count := fun nu i z => round3Parameter_primary_count_transport Data i.2 nu (U i)
      (out nu i) (theta i) (hSupport' i) (fun a => (hLift nu i a).2.2.1)
      (5^Module.finrank ℝ (Ep × D)) (hCount nu i) z }
  exact ⟨{
    packet := packet
    mu := mu
    Mb := Mb
    buffer := buffer
    mu_pos := hmu
    Mb_nonneg := hMb
    buffer_pos := hbuffer
    native_first := hFirst
    native_higher := hHigher
    native_inverse := hInverse
    observer := hObserver
    cutoff_eq := hCutoffEq
    cutoff_jets := hCutoffJets
    radius := R
    radius_pos := hR
    centers := hcenters
    center_active := hCenterPhysical
    total_card := hcard },hMbEq,hBufferLe⟩


end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_counted_primary_pieces_from_low_phase_budget
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_open_counted_primary_supply_from_finite_low_phase_budget
