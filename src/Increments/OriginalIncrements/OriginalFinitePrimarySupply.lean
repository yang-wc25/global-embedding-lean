import OriginalIncrements.OriginalFinitePrimaryObserverRefinement
import Repair.FullIncrementNovOpenPrimaryPieces

/-!
# The actual primary packet retains its original finite budgets

The packet here is constructed from the same original compact parent,
phase and parameter neighborhood as the literal raw supplier. Its cutoffs,
centers, charts, manifold slices, overlap certificate and ordinary partition
germs are retained. The named positive observer budgets and exact grid-cutoff
jet formula are attached to those very pieces, not to an unrelated local
choice. The object is chosen before every later scale and derivative order.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
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

theorem original_primary_pieces_with_finite_budgets
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
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source) :
    ∃ (mu Mb buffer : ℝ) (s : Finset X) (out : s → Round3PreparedPrimaryPiece Data i.2 nu W),
      0 < mu ∧ 0 ≤ Mb ∧ 0 < buffer ∧
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
          (actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost X j) := by
  obtain ⟨mu,Mb,buffer,s,b,e,eta,Bnative,hmu,hMb,hbuffer,hB,hBpos,
    hData,hOpen,hWsource,hActive,hCompactEta,hSmoothEta,hSupportEta,hPartition,hGerm,
    hCount,hNative,hCutoffEq,hCutoffJets,hHigher,hInverse,hObserver⟩ :=
    original_primary_refinement_with_finite_observer_budgets
      Data hd hs hp i nu W hW hParam hOriginal theta hCompact hTheta hThetaSupport
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
  exact ⟨mu,Mb,buffer,s,out,hmu,hMb,hbuffer,fun _ => rfl,
    fun a _ hz => (hSupportEta a hz).2,hGerm,hCount,
    (fun a => by simpa only [hB] using hNative a),hHigher,hInverse,hObserver,hCutoffEq,hCutoffJets⟩

/-- The standard actual primary supplier retains the proved finite original
observer budgets and exact grid cutoff formula for its own pieces. -/
structure OriginalBudgetedPrimarySupply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ) where
  packet : Round3ParameterWholePrimaryPieceSupply Data theta
  mu : Fin Data.primaryCount → (Fin Data.atlas.count × Fin Data.parameterCount) → ℝ
  Mb : Fin Data.primaryCount → (Fin Data.atlas.count × Fin Data.parameterCount) → ℝ
  buffer : Fin Data.primaryCount → (Fin Data.atlas.count × Fin Data.parameterCount) → ℝ
  mu_pos : ∀ nu i, 0 < mu nu i
  Mb_nonneg : ∀ nu i, 0 ≤ Mb nu i
  buffer_pos : ∀ nu i, 0 < buffer nu i
  native_first : ∀ nu i a, ∀ x ∈ (packet.piece nu i a).native.source,
    ‖fderiv ℝ (packet.piece nu i a).native x‖ ≤ 2*(1+2*Mb nu i)
  native_higher : ∀ nu i a k, 1 ≤ k → ∀ x ∈ (packet.piece nu i a).native.source,
    ‖iteratedFDeriv ℝ (k+1) (packet.piece nu i a).native x‖ ≤
      2^(k+2)*‖iteratedFDeriv ℝ (k+1)
        ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘
          (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) x‖
  native_inverse : ∀ nu i a (S : Set X), S ⊆ (packet.piece nu i a).native.target →
    ∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
    (∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ (packet.piece nu i a).native.symm '' S,
      weight^k*‖iteratedFDeriv ℝ (k+1)
        ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘
          (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) x‖ ≤ Mj) →
    ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ S,
      weight^(k-1)*‖iteratedFDeriv ℝ k (packet.piece nu i a).native.symm y‖ ≤
        actualEuclideanPhaseSampleInverseJetCost (mu nu i) (Mb nu i) Mj j
  observer : ∀ nu i a, OriginalRefinementObserverBudgets Data i nu (mu nu i) (Mb nu i)
    (packet.piece nu i a).native
  cutoff_eq : ∀ nu i a, (packet.piece nu i a).cutoff = actualHostRefinementCutoff
    (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1))
    (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
    (actualRefinementCutoff X (packet.s nu i)
      (buffer nu i/actualPhaseRefinementFactor (mu nu i) (Mb nu i)) a.val)
  cutoff_jets : ∀ nu i (j : ℕ) (weight : ℝ), 0 ≤ weight → weight ≤ buffer nu i →
    ∀ (a : packet.s nu i) (x : X), weight^j*‖iteratedFDeriv ℝ j
      (actualRefinementCutoff X (packet.s nu i)
        (buffer nu i/actualPhaseRefinementFactor (mu nu i) (Mb nu i)) a.val) x‖ ≤
      (actualPhaseRefinementFactor (mu nu i) (Mb nu i))^j*actualRefinementCutoffJetCost X j

theorem original_open_primary_supply_with_finite_budgets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) :
    Nonempty (OriginalBudgetedPrimarySupply Data theta) := by
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
  have hPieces (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    original_primary_pieces_with_finite_budgets Data hd hs hp i nu (W i) (hW i)
      (fun _ hy => hy.1.1) (fun z hz => ⟨hz.1.2,mem_univ _⟩)
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      (hNative i).2.1 (hNative i).1 (hNSupport i)
  choose mu Mb buffer s piece hmu hMb hbuffer hHost hParent hGerm hCount hFirst hHigher hInverse hObserver hCutoffEq hCutoffJets using hPieces
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
    cutoff_jets := hCutoffJets }⟩


end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_primary_pieces_with_finite_budgets
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_open_primary_supply_with_finite_budgets
