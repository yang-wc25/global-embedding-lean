import FaithfulIncrements.QuantitativeHostRefinement
import OriginalIncrements.OriginalFiniteLowPhasePreparation
import Probes.Round3PreparedPrimaryPhase
import Probes.ActualRelativeInteractionCarrier
import Probes.Round3PreparedInteractionGerms

/-!
# The actual primary refinement retains an explicit original low budget

The low bounds on the actual parent carrier are supplied by
`original_parameter_localization_with_finite_phase_budget`. The very same
finite charts and exact cutoffs are constructed with
`Mb = originalLowPhaseBudget m d Packet`, with a buffer no larger than the
chosen original scale. The fixed-data spatial margin is produced from the
original primary Good condition; it is not a new caller input.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
open FaithfulIncrements
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [T2Space M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem original_low_budget_primary_refinement
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
    ∃ (mu Mb buffer : ℝ) (s : Finset X) (b : s → OpenPartialHomeomorph X X)
      (e : s → Ep → OpenPartialHomeomorph M D) (eta : s → Ep × M → ℝ) (Bnative : ℝ),
      0 < mu ∧ 0 ≤ Mb ∧ 0 < buffer ∧ Bnative = 2*(1+2*Mb) ∧ 0 < Bnative ∧
      (∀ a : s, ActualOriginalHostSliceData (Data.atlas.chart i.1) (b a)
        (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e a)) ∧
      (∀ a : s, (b a).source ⊆ actualOriginalNativeOpen Data i) ∧
      (∀ a : s, (actualHostAdaptedChart (Data.atlas.chart i.1) (b a)).source ⊆ W) ∧
      (∀ a : s, ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) (b a)).source,
        ((Data.parameterChart i.2).symm w.1,w.2) ∈
          Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ a : s, IsCompact (tsupport (eta a))) ∧
      (∀ a : s, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (eta a)) ∧
      (∀ a : s, tsupport (eta a) ⊆
        (actualHostAdaptedChart (Data.atlas.chart i.1) (b a)).source ∩ tsupport theta) ∧
      (∀ y ∈ incrementsGlobalRelativeSupport W
          (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)),
        ∑ a : s, eta a y = theta y) ∧
      (∀ y ∈ incrementsGlobalRelativeSupport W
          (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)),
        ∀ᶠ w in 𝓝 y, ∑ a : s, eta a w = theta w) ∧
      (∀ y, (Finset.univ.filter (fun a : s => y ∈ tsupport (eta a))).card ≤ 5^Module.finrank ℝ X) ∧
      (∀ a : s, ∀ z ∈ (b a).source, ‖fderiv ℝ (b a) z‖ ≤ Bnative) ∧
      (∀ a : s, eta a = actualHostRefinementCutoff
        (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) theta
        (actualRefinementCutoff X s (buffer/actualPhaseRefinementFactor mu Mb) a.val)) ∧
      (∀ (j : ℕ) (weight : ℝ), 0 ≤ weight → weight ≤ buffer → ∀ (a : s) (x : X),
        weight^j*‖iteratedFDeriv ℝ j
          (actualRefinementCutoff X s (buffer/actualPhaseRefinementFactor mu Mb) a.val) x‖ ≤
          (actualPhaseRefinementFactor mu Mb)^j * actualRefinementCutoffJetCost X j) ∧
      (∀ (a : s) k, 1 ≤ k → ∀ x ∈ (b a).source,
        ‖iteratedFDeriv ℝ (k+1) (b a) x‖ ≤
          2^(k+2)*‖iteratedFDeriv ℝ (k+1)
            ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘
              (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) x‖) ∧
      (∀ (a : s) (S : Set X), S ⊆ (b a).target → ∀ (j : ℕ) (weight Mj : ℝ),
        0 < weight → 0 ≤ Mj →
        (∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ (b a).symm '' S,
          weight^k*‖iteratedFDeriv ℝ (k+1)
            ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘
              (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) x‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ S,
          weight^(k-1)*‖iteratedFDeriv ℝ k (b a).symm y‖ ≤
            actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j) ∧
      Mb = originalLowPhaseBudget m d Packet ∧ buffer ≤ ell := by
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
  let pull : Ep × M → P × M := fun z => ((Data.parameterChart i.2).symm z.1,z.2)
  let primary := incrementsGlobalRelativeSupport W (fun z => Data.cutoff nu (pull z))
  have hPull : ContinuousOn pull W :=
    ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn hParam).prodMk
      continuous_snd.continuousOn
  have hPullSupport : primary ⊆ pull ⁻¹' incrementsOriginalRelativeCutoffSupport Data nu :=
    actual_relative_support_pullback_subset W (incrementsOriginalParameterRegion Data)
      pull hPull hOriginal (Data.cutoff nu)
  let carrier := tsupport theta ∩ primary
  have hCarrier : IsCompact carrier := by
    dsimp only [carrier,primary,incrementsGlobalRelativeSupport]
    simpa only [Set.inter_self] using actual_compact_interaction_carrier
      (tsupport theta) W hCompact (fun y hy => (hThetaSupport hy).1)
      (fun z => Data.cutoff nu (pull z)) (fun z => Data.cutoff nu (pull z))
  have hCarrierSource : carrier ⊆ q.source := fun y hy => (hThetaSupport hy.1).2
  let K := q '' carrier
  have hK : IsCompact K := hCarrier.image_of_continuousOn (q.continuousOn.mono hCarrierSource)
  let U := (q.target ∩ q.symm ⁻¹' W) ∩ actualOriginalPrimaryNativeOpen Data nu i
  have hU : IsOpen U :=
    (q.symm.continuousOn.isOpen_inter_preimage q.open_target hW).inter
      (actualOriginalPrimaryNativeOpen_isOpen Data hd nu i)
  have hKU : K ⊆ U := by
    rintro _ ⟨y,hy,rfl⟩
    have hyW := (hThetaSupport hy.1).1
    have hyq := hCarrierSource hy
    have hsup := hPullSupport hy.2
    have hpull : ((Data.parameterChart i.2).symm (q y).1,(Data.atlas.chart i.1).symm (q y).2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := by
      change ((Data.parameterChart i.2).symm y.1,(Data.atlas.chart i.1).symm ((Data.atlas.chart i.1) y.2)) ∈ _
      rw [(Data.atlas.chart i.1).left_inv hyq.2]
      exact ⟨hd.cutoff_support_local nu hsup,incrementsOriginalRelativeCutoffSupport_subset Data nu hsup⟩
    exact ⟨⟨q.map_source hyq,by change q.symm (q y) ∈ W; rwa [q.left_inv hyq]⟩,
      round3_prepared_native_primary_mem Data i nu (q y) (q.map_source hyq).2 (hParam y hyW) hpull⟩
  have hNativeLow : ∀ k, k ≤ 1 → ∀ x ∈ K,
      ell^k*‖iteratedFDeriv ℝ (k+1) (originalNativePrimaryPhase Data nu i) x‖ ≤
        actualOriginalTotalPhaseJetCost (m+1) d k*Packet k+1 := by
    intro k hk x hx
    obtain ⟨w,hw,rfl⟩ := hx
    exact hLow k hk w hw.1 hw.2
  obtain ⟨mu,R,buffer,O,hmu,hR,hbuffer,hBufferEll,hO,hKO,hOU,hKR,hbufferO,hPsi,hnoncrit,hfirst,hsecond⟩ :=
    original_primary_phase_preparation_from_finite_low_jets Data hd hs hp i nu K U hK hU hKU
      (fun _ hz => hz.2) ell hell Packet hNativeLow
  let Mb := originalLowPhaseBudget m d Packet
  have hMb : 0 ≤ Mb := (originalLowPhaseBudget_pos m d Packet).le
  have hRelative : incrementsGlobalRelativeSupport W theta = W ∩ tsupport theta :=
    parameterRound2_global_relativeSupport_eq W hW theta
  have hRelativeSource : incrementsGlobalRelativeSupport W theta ⊆ q.source := by
    rw [hRelative]
    exact fun _ hz => (hThetaSupport hz.2).2
  obtain ⟨s,b,e,hdata,hbO,hSourceW,hCompactEta,hSmoothEta,hSupportEta,hPartition,hGerm,hCount,
      hNativeBound,hCutBudget,hHigher,hInverse⟩ :=
    quantitative_host_interaction_refinement mu Mb R buffer hmu hMb hbuffer
      (Data.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1) theta
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2))
      W primary hW hTheta.contMDiffOn K O 0
      hRelativeSource (fun y hy => ⟨y,⟨(hRelative ▸ hy.1).2,hy.2⟩,rfl⟩)
      hO hKR (fun _ hz => (hOU hz).1.1) (fun _ hz => (hOU hz).1.2)
      hbufferO hPsi hnoncrit hfirst hsecond
  let radius := buffer/actualPhaseRefinementFactor mu Mb
  let eta := fun a : s => actualHostRefinementCutoff q theta (actualRefinementCutoff X s radius a.val)
  have hPrimary (a : s) (y : Ep × M)
      (hy : y ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) (b a)).source) :
      pull y ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := by
    have hh := round3_prepared_native_primary_active Data i nu (hOU (hbO a hy.2)).2
    change ((Data.parameterChart i.2).symm y.1,(Data.atlas.chart i.1).symm ((Data.atlas.chart i.1) y.2)) ∈ _ at hh
    rwa [(Data.atlas.chart i.1).left_inv hy.1.2] at hh
  have hPrimaryW (y : Ep × M) (hy : y ∈ primary) : y ∈ W := by
    obtain ⟨z,_,rfl⟩ := hy
    exact z.property
  refine ⟨mu,Mb,buffer,s,b,e,eta,2*(1+2*Mb),hmu,hMb,hbuffer,rfl,by positivity,hdata,
    fun a _ hz => round3_prepared_primary_native_subset Data i nu (hOU (hbO a hz)).2,
    hSourceW,hPrimary,hCompactEta,hSmoothEta,?_,?_,?_,hCount,hNativeBound,
    (fun _ => rfl),hCutBudget,hHigher,hInverse,rfl,hBufferEll⟩
  · intro a y hy
    exact ⟨(hSupportEta a hy).1,(hRelative ▸ (hSupportEta a hy).2).2⟩
  · intro y hy
    exact hPartition y ⟨hPrimaryW y hy,hy⟩
  · intro y hy
    exact hGerm y ⟨hPrimaryW y hy,hy⟩

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_low_budget_primary_refinement
