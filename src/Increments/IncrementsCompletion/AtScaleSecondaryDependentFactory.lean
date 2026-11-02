import Repair.FullIncrementNovOpenSecondaryPartition
import IncrementsCompletion.AtScaleSecondaryRestriction
import IncrementsCompletion.AtScaleSecondaryPacketProfiles
import IncrementsCompletion.AtScaleSecondaryPacketRaw
import IncrementsCompletion.AtScaleSecondaryNumerics
import Repair.AuxBridgeNovSecondaryRestriction
import IncrementsCompletion.AtScaleSecondaryFamily
import Probes.Round3ParameterSecondaryRawReindex

/-! The true dependent secondary family is constructed from current-scale
profiles of the same actual packet. Its displayed numerical geometry cost
is fixed before ell and the profile certificate. No all-scale raw record,
replacement phase, or norm-domain compactness is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance incrementsPositiveFactorySignedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem incrementsCompletion_at_scale_secondary_dependent_factory
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (V0 : Set P) (hPart : ∀ z : P × M, z.1 ∈ V0 → ∑ i, theta i z = 1)
    (L : ℕ) (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (Tinv Kcut Tobs : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hKcut : ∀ k, 0 ≤ Kcut k) (hTobs : ∀ k, 0 ≤ Tobs k)
    (q : ℕ) (c : ℝ) (InputBudget : ℕ → ℝ) :
    let Sub := fun r => Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(packet.s r i))
    letI : ∀ r, Fintype (Sub r) := fun r => inferInstance
    let Mrest := incrementsCompletionAtScaleSecondaryGeometryCost Data hd hs theta packet Tinv Tobs q c InputBudget
    let Cut := fun j => Kcut (actualSecondarySolveOrder q j)
    ∀ ell, 0 < ell → ell ≤ 1 →
    IncrementsCompletionAtScaleSecondaryPacketProfiles Data hd hs theta packet ell Tinv Kcut Tobs →
    ∀ Mnew : ℕ → ℝ, (∀ j, Mrest j ≤ Mnew j) →
    ∀ (G : Set (P × M)) (hG : IsOpen G), (∀ z ∈ G, z.1 ∈ V0) →
    ∀ baseIndex : Fin Data.atlas.count × Fin Data.parameterCount,
    let W := round3ParameterNativeDomain (Data.parameterChart baseIndex.2) G
    IncrementsOriginalCoordinateEllipticityInputs Data c →
    (∀ n, incrementsOriginalCoreInputProfile Data n ell ≠ ⊤) →
    (∀ n, (incrementsOriginalCoreInputProfile Data n ell).toReal ≤ InputBudget n) →
    ∀ (Β : Type*) [Fintype Β]
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
        (Λ := Fin Data.primaryCount) (Β := Β) (actualOriginalOpenParameterSlice Data baseIndex)),
    (∀ nu, g.phase nu = fun z : Ep × M => Data.phase nu ((Data.parameterChart baseIndex.2).symm z.1,z.2)) →
    (∀ nu, g.cutoff nu = fun z : Ep × M => Data.cutoff nu ((Data.parameterChart baseIndex.2).symm z.1,z.2)) →
    ActualOriginalPrimaryPhysicalGeometry (actualOriginalOpenParameterSlice Data baseIndex)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex) g →
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞
      (fun y : Ep × M => actualOriginalOpenParameterSlice Data baseIndex y.1 y.2) W →
    ∃ family : Round3ParameterDependentSecondaryFamily Data Sub
      (actualOriginalOpenParameterSlice Data baseIndex)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex) g q ell W W
      Mnew Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D)) (round3ParameterOriginalNativeSamplesAt Data baseIndex.2),
      family.choice = fun r a =>
        (((round3PreparedParameterSecondaryChoice Data hd hs a.1 r _ (packet.piece r a.1 a.2)).restrictOpen G hG).pullback
          (Data.parameterChart baseIndex.2)).toNative := by
  intro Sub
  letI : ∀ r, Fintype (Sub r) := fun r => inferInstance
  intro Mrest Cut ell hell hell1 profiles
  let Ti := Tinv
  let Tc := Kcut
  let To := Tobs
  have hTi0 := hTinv
  have hTc0 := hKcut
  have hTo0 := hTobs
  have hRaw := incrementsCompletion_at_scale_secondary_raw_pieces Data hd hs hImm theta packet
    hSupport ell hell hell1 Ti Tc To hTi0 hTc0 hTo0 profiles.positive profiles.cutoff
  choose raw hChoice hTi hTc hTo hcT hB using hRaw
  let A := Sigma Sub
  intro Mnew hMnew G hG hGV baseIndex W hEll hFinite hBudget Β _ g hPhase hCutoff primaryGeometry hOriginal
  let U := (Data.parameterChart baseIndex.2).target ×ˢ (univ : Set M)
  have hW : IsOpen W := round3Parameter_nativeDomain_open _ _ hG
  have hWU : W ⊆ U := fun z hz => ⟨hz.1,mem_univ _⟩
  have hU : IsOpen U := (Data.parameterChart baseIndex.2).open_target.prod isOpen_univ
  let rawG := fun r i (a : packet.s r i) =>
    (raw r i a baseIndex.2).restrictOpen W hW hWU hU
  let piece := fun r (a : Sub r) => incrementsCompletion_at_scale_secondary_piece_reindex
    Data hd hs (a.1.1,baseIndex.2) r W ell
      (fun v : Fin Data.atlas.count => Data.atlas.chart v)
      (fun v => (parameterTensorModelEquiv (m+1) d) ⁻¹'
        incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (v,baseIndex.2))
      (rawG r a.1 a.2) (fun v : Fin Data.atlas.count × Fin Data.parameterCount => v.1)
  let physical := fun r (a : Sub r) => round3PreparedParameterSecondaryChoice Data hd hs a.1 r _ (packet.piece r a.1 a.2)
  let choice := fun r a => (((physical r a).restrictOpen G hG).pullback (Data.parameterChart baseIndex.2)).toNative
  have hChoice' (r) (a : Sub r) : (piece r a).choice = choice r a := by
    change (raw r a.1 a.2 baseIndex.2).choice.restrictOpen W hW = _
    rw [hChoice]
    exact (auxBridgeNov_secondary_native_restriction_commutes (physical r a) (Data.parameterChart baseIndex.2) G hG).symm
  have hPartCount := fullIncrementNov_secondary_local_partition_count Data hd hs theta packet V0 hPart L hCount
    G hG hGV baseIndex.2 baseIndex.1
  have hCarrier (r) (a : Sub r) : (piece r a).carrier = tsupport (choice r a).cutoff ∩
      actualOriginalParameterSupportPair Data baseIndex r.val.1.1 r.val.1.2 W := by
    rw [(piece r a).carrier_eq,hChoice']
    rfl
  have hPartPieces (r) (y) (hy : y ∈ actualOriginalParameterSupportPair Data baseIndex r.val.1.1 r.val.1.2 W) :
      ∑ a : Sub r, (piece r a).choice.cutoff y = 1 := by
    simp_rw [hChoice']
    exact hPartCount.1 r y hy
  have hCountPieces (r) (y) : (Finset.univ.filter (fun a : Sub r => y ∈ (piece r a).carrier)).card ≤
      L*5^Module.finrank ℝ (Ep × D) := by
    simp_rw [hCarrier]
    exact hPartCount.2 r y
  have hCost (j) (r) (a : Sub r) : round3PreparedGeometryCost m d N (piece r a).Tinv
      (piece r a).cT (piece r a).Bnative (actualSecondarySolveOrder q j) (j+1)
      (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c ≤ Mrest j := by
    change round3PreparedGeometryCost m d N (raw r a.1 a.2 baseIndex.2).Tinv
      (raw r a.1 a.2 baseIndex.2).cT (raw r a.1 a.2 baseIndex.2).Bnative _ _ _ _ ≤ _
    rw [hTi,hcT,hB]
    exact round3PreparedFiniteMaximum_bound (fun aa : A =>
      round3PreparedGeometryCost m d N Ti (packet.piece aa.1 aa.2.1 aa.2.2).cT (1+To 1)
        (actualSecondarySolveOrder q j) (j+1) (InputBudget (max (actualSecondarySolveOrder q j) (j+1))) c)
      (⟨r,a⟩ : A)
  obtain ⟨family,hFamily⟩ := incrementsCompletion_at_scale_dependent_secondary_from_raw Data hd hs baseIndex Sub
    (fun _ a => a.1.1) W W ell piece hPartPieces (L*5^Module.finrank ℝ (Ep × D)) hCountPieces
    q c hell hell1 hEll InputBudget hFinite hBudget Mnew Cut Ti To
    (fun j r a => (hCost j r a).trans (hMnew j))
    (fun j r a => by change (raw r a.1 a.2 baseIndex.2).Kcut _ ≤ _; rw [hTc])
    (fun k r a => by change (raw r a.1 a.2 baseIndex.2).Tinv k ≤ _; rw [hTi])
    (fun k r a => by change (raw r a.1 a.2 baseIndex.2).Tobs k ≤ _; rw [hTo])
    g hPhase hCutoff primaryGeometry hOriginal
  refine ⟨family,hFamily.trans ?_⟩
  funext r a
  exact hChoice' r a

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_secondary_dependent_factory
