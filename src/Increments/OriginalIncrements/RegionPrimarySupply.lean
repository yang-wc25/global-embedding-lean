import OriginalCollars.RegionPrimaryPieces
import OriginalCollars.PrimaryPlateauCarrier

/-!
# A same primary packet manufactured at common original geometric numbers

The actual grid is run with common mu, Mb, R and buffer. All original
packet fields, exact cutoffs, observer profiles, active-center witnesses,
and the numerical total cardinality are retained. In particular this is
not a relabeling of the arbitrarily chosen constants in an older packet.
The input bounds are on the original scalar phase and original domains;
no bound on a selected inverse or final displacement is an assumption.
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

theorem original_open_counted_primary_supply_with_region
    (mu Mb R buffer : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hR : 0 < R) (hbuffer : 0 < buffer)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1)
    (O : Fin Data.primaryCount → Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (hO : ∀ nu i, IsOpen (O nu i))
    (hONative : ∀ nu i, O nu i ⊆ actualOriginalPrimaryNativeOpen Data nu i)
    (hRadius : ∀ nu i, originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆ closedBall 0 R)
    (hBuffer : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) → ball x buffer ⊆ O nu i)
    (hNoncritical : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) →
      mu ≤ ‖(fderiv ℝ (originalNativePrimaryPhase Data nu i) x).comp
        (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hFirst : ∀ nu i x, x ∈ O nu i →
      ‖fderiv ℝ (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb)
    (hSecond : ∀ nu i x, x ∈ O nu i →
      buffer*‖iteratedFDeriv ℝ 2 (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb) :
    ∃ supply : OriginalCountedPrimarySupply Data theta,
      (∀ nu i, supply.mu nu i = mu) ∧
      (∀ nu i, supply.Mb nu i = Mb) ∧
      (∀ nu i, supply.buffer nu i = buffer) ∧
      (∀ nu i, supply.radius nu i = R) ∧
      (∀ nu i a, (supply.packet.piece nu i a).Bnative = 2*(1+2*Mb)) ∧
      (∀ nu i a, (supply.packet.piece nu i a).native.source ⊆ O nu i) := by
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
  have hCarrierSubset (nu : Fin Data.primaryCount)
      (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) ''
        (tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ∩
          incrementsGlobalRelativeSupport (W i)
            (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2))) ⊆
      originalNativePrimaryCarrier Data i nu
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) := by
    rintro z ⟨y,hy,rfl⟩
    refine ⟨y,⟨hy.1,?_⟩,rfl⟩
    exact actual_relative_support_pullback_subset (W i) (U i) id continuous_id.continuousOn
      (fun z hz => ⟨hz.1.1,hz.2⟩)
      (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)) hy.2
  have hOParent (nu : Fin Data.primaryCount)
      (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      MapsTo (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm
        (O nu i) (W i) := by
    intro z hz
    have hh := (round3Parameter_originalNativeOpen_iff Data i z).mp
      (round3_prepared_primary_native_subset Data i nu (hONative nu i hz))
    exact ⟨⟨hh.2.1,hh.2.2⟩,mem_univ _⟩
  have hPieces (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    original_counted_primary_pieces_with_region mu Mb R buffer hmu hMb hbuffer
      Data hd hs i nu (W i) (hW i)
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      (hNative i).2.1 (hNative i).1 (hNSupport i)
      (O nu i) (hO nu i) (hONative nu i) (hOParent nu i)
      ((hCarrierSubset nu i).trans (hRadius nu i))
      (fun x hx => hBuffer nu i x (hCarrierSubset nu i hx))
      (fun x hx => hNoncritical nu i x (hCarrierSubset nu i hx))
      (hFirst nu i) (hSecond nu i)
  choose s piece hcard hcenters hCentersActive hHost hParent hGerm hCount hFirstOut
    hHigher hInverse hObserver hCutoffEq hCutoffJets hBnative hNativeRegion using hPieces
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
    mu := fun _ _ => mu
    Mb := fun _ _ => Mb
    buffer := fun _ _ => buffer
    mu_pos := fun _ _ => hmu
    Mb_nonneg := fun _ _ => hMb
    buffer_pos := fun _ _ => hbuffer
    native_first := hFirstOut
    native_higher := hHigher
    native_inverse := hInverse
    observer := hObserver
    cutoff_eq := hCutoffEq
    cutoff_jets := hCutoffJets
    radius := fun _ _ => R
    radius_pos := fun _ _ => hR
    centers := hcenters
    center_active := hCenterPhysical
    total_card := hcard },fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,hBnative,hNativeRegion⟩

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_open_counted_primary_supply_with_region
