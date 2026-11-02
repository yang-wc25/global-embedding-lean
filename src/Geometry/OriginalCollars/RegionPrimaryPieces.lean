import OriginalCollars.CommonGeometryPrimaryPieces
import Probes.Round3ParameterCrossNativeData

/-!
# Run the counted primary grid at the prescribed common original numbers

Unlike the qualitative wrapper, this producer does not choose new mu or
buffer witnesses by compactness. It runs the actual counted grid at the
given original-coordinate noncritical reserve, original-domain buffer and
two original phase-jet bounds. Its exact cutoff, observer inverse profiles,
and total cardinality therefore refer to those same common numbers.

These are internal original-coordinate inputs. The actual factory carrier
and covector-transport producers supply them; no adapted inverse, selected
cutoff estimate, conditioned frame or final displacement is an input.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
open OriginalCollars
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem original_counted_primary_pieces_with_region
    (mu Mb R buffer : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (theta : Ep × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hTheta : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta)
    (hThetaSupport : tsupport theta ⊆ W ∩
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source)
    (O : Set X) (hO : IsOpen O)
    (hONative : O ⊆ actualOriginalPrimaryNativeOpen Data nu i)
    (hParent : MapsTo (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm O W)
    (hRadius : (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) ''
      (tsupport theta ∩ incrementsGlobalRelativeSupport W
        (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2))) ⊆
      closedBall 0 R)
    (hBuffer : ∀ x ∈ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) ''
      (tsupport theta ∩ incrementsGlobalRelativeSupport W
        (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2))),
      ball x buffer ⊆ O)
    (hNoncritical : ∀ x ∈ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) ''
      (tsupport theta ∩ incrementsGlobalRelativeSupport W
        (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2))),
      mu ≤ ‖(fderiv ℝ (originalNativePrimaryPhase Data nu i) x).comp
        (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hFirst : ∀ x ∈ O, ‖fderiv ℝ (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb)
    (hSecond : ∀ x ∈ O, buffer*‖iteratedFDeriv ℝ 2 (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb) :
    ∃ (s : Finset X) (out : s → Round3PreparedPrimaryPiece Data i.2 nu W),
      s.card ≤ originalPhaseTotalPieceBudget («Ep» := Ep) (m := m) mu Mb R buffer hmu hMb hbuffer ∧
      (↑s : Set X) ⊆ closedBall 0 R ∧
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
      (∀ a : s, (out a).Bnative = 2*(1+2*Mb)) ∧
      (∀ a : s, (out a).native.source ⊆ O) := by
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
  let primary := incrementsGlobalRelativeSupport W
    (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2))
  let K := q '' (tsupport theta ∩ primary)
  have hRelative : incrementsGlobalRelativeSupport W theta = W ∩ tsupport theta :=
    parameterRound2_global_relativeSupport_eq W hW theta
  have hRelativeSource : incrementsGlobalRelativeSupport W theta ⊆ q.source := by
    rw [hRelative]
    exact fun z hz => (hThetaSupport hz.2).2
  have hOq : O ⊆ q.target := by
    intro z hz
    have hh := (round3Parameter_originalNativeOpen_iff Data i z).mp
      (round3_prepared_primary_native_subset Data i nu (hONative hz))
    exact ⟨mem_univ _,hh.1⟩
  have hPsi : ContDiffOn ℝ ∞ (originalNativePrimaryPhase Data nu i) O :=
    (round3_actual_original_primary_native_phase_smooth Data hd hs nu i).mono hONative
  obtain ⟨s,b,e,hcard,hsK,hdata,hbO,hSourceW,hCompactEta,hSmoothEta,hSupportEta,
      hPartition,hGerm,hCount,hNative,hCutoffJets,hHigher,hInverse⟩ :=
    counted_host_interaction_refinement mu Mb R buffer hmu hMb hbuffer
      (Data.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1) theta
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2))
      W primary hW hTheta.contMDiffOn K O 0 hRelativeSource
      (fun y hy => ⟨y,⟨(hRelative ▸ hy.1).2,hy.2⟩,rfl⟩)
      hO hRadius hOq hParent hBuffer hPsi hNoncritical hFirst hSecond
  have hCenters (a : s) : q.symm a.val ∈ tsupport theta ∩ primary := by
    obtain ⟨y,hy,heq⟩ := hsK a.property
    rw [← heq,q.left_inv (hThetaSupport hy.1).2]
    exact hy
  have hActive (a : s) (y : Ep × M)
      (hy : y ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) (b a)).source) :
      ((Data.parameterChart i.2).symm y.1,y.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := by
    have hh := round3_prepared_native_primary_active Data i nu (hONative (hbO a hy.2))
    change ((Data.parameterChart i.2).symm y.1,
      (Data.atlas.chart i.1).symm ((Data.atlas.chart i.1) y.2)) ∈ _ at hh
    rwa [(Data.atlas.chart i.1).left_inv hy.1.2] at hh
  let eta := fun a : s => actualHostRefinementCutoff q theta
    (actualRefinementCutoff X s (buffer/actualPhaseRefinementFactor mu Mb) a.val)
  have hObserver (a : s) : OriginalRefinementObserverBudgets Data i nu mu Mb (b a) :=
    original_refinement_observer_budgets_of_actual_jets Data hd hs i nu mu Mb hmu hMb
      (b a) (e a) (hdata a) (hNative a) (hHigher a) (hInverse a)
  let out := fun a : s => ({
    host := i.1
    native := b a
    slices := e a
    cutoff := eta a
    data := hdata a
    native_source := fun z hz =>
      round3_prepared_primary_native_subset Data i nu (hONative (hbO a hz))
    source_domain := hSourceW a
    active := hActive a
    compact := hCompactEta a
    smooth := hSmoothEta a
    support := fun z hz => (hSupportEta a hz).1
    Bnative := 2*(1+2*Mb)
    positive := by positivity
    native_first := hNative a } : Round3PreparedPrimaryPiece Data i.2 nu W)
  refine ⟨s,out,hcard,hsK.trans hRadius,hCenters,fun _ => rfl,?_,?_,hCount,hNative,
    hHigher,hInverse,hObserver,fun _ => rfl,hCutoffJets,fun _ => rfl,hbO⟩
  · intro a y hy
    exact (hRelative ▸ (hSupportEta a hy).2).2
  · intro y hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact hGerm z.val ⟨z.property,⟨z,hz,rfl⟩⟩

end GlobalEmbedding.Continuation.OriginalIncrements

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_counted_primary_pieces_with_region
