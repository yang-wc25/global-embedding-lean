import Probes.Round3PreparedOriginalPrimaryPacket
import Probes.Round3PreparedPrimarySamples
import Probes.Round3PreparedReferenceTargetProfiles

/-! One complete actual reference primary packet. All quantitative geometry
and all-order refinement profiles are chosen from the reference input before
any perturbing map or smoothing scale. The producer supplies every field
from the original Data, its genuine raw source preparation and coordinate
bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
universe uB
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)
private local instance packetFirstNormed : NormedAddCommGroup (D →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance packetFirstSpace : NormedSpace ℝ (D →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance packetHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance packetHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance

structure Round3PreparedReferencePrimaryPacket
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (Β : Type uB) [Fintype Β] (Rsub : ℕ) where
  parameterDomain : Set Ep
  parameter_open : IsOpen parameterDomain
  parameter_contains : Data.parameterSet ⊆ parameterDomain
  parameter_subset : parameterDomain ⊆ Data.parameterOpen
  piece : ∀ nu : Fin Data.primaryCount, Β →
    Round3PreparedPrimaryPiece Data baseIndex.2 nu (Data.parameterOpen ×ˢ (univ : Set M))
  cF : ℝ
  cT : ℝ
  MH : ℝ
  Bnative : ℝ
  cF_pos : 0 < cF
  cT_pos : 0 < cT
  MH_nonneg : 0 ≤ MH
  Bnative_pos : 0 < Bnative
  native_bound : ∀ nu a, (piece nu a).Bnative = Bnative
  inner : ∀ nu a y, y ∈ tsupport (piece nu a).cutoff → y.2 ∈ Data.atlas.inner (piece nu a).host
  source_inner : ∀ nu a y, y ∈ (actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native).source →
    y.2 ∈ Data.atlas.inner (piece nu a).host
  first : ∀ nu a z, z ∈ (piece nu a).native.target → ∀ v : D,
    cF*‖v‖^2 ≤ ‖fderiv ℝ (actualOriginalOpenParameterSlice Data baseIndex z.1 ∘
      ((piece nu a).slices z.1).symm) z.2 v‖^2
  transverse : ∀ nu a z, z ∈ (piece nu a).native.target → ∀ v : Tdata,
    cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
      (actualOriginalOpenParameterSlice Data baseIndex z.1)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex z.1)
      ((piece nu a).slices z.1).symm z.2 v‖^2
  hessian : ∀ nu a z, z ∈ (piece nu a).native.target →
    ‖fderiv ℝ (fderiv ℝ (actualOriginalOpenParameterSlice Data baseIndex z.1 ∘
      ((piece nu a).slices z.1).symm)) z.2‖ ≤ MH
  Tchart : ℕ → ℝ
  Tchart_nonneg : ∀ j, 0 ≤ Tchart j
  Tforward : ℕ → ℝ
  Tforward_nonneg : ∀ j, 0 ≤ Tforward j
  chart_jets_target : ∀ nu a j z, z ∈ (piece nu a).native.target →
    ‖iteratedFDeriv ℝ j (piece nu a).native.symm z‖ ≤ Tchart j
  forward_jets_source : ∀ nu a j z, z ∈ (piece nu a).native.source →
    ‖iteratedFDeriv ℝ j (piece nu a).native z‖ ≤ Tforward j
  chart_jets : ∀ nu a j y, y ∈ tsupport (piece nu a).cutoff →
    ‖iteratedFDeriv ℝ j (piece nu a).native.symm
      (actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native y)‖ ≤ Tchart j
  Tinv : ℕ → ℝ
  Forward : ℕ → ℝ
  Meta : ℕ → ℝ
  Tinv_nonneg : ∀ j, 0 ≤ Tinv j
  Forward_nonneg : ∀ j, 0 ≤ Forward j
  Meta_nonneg : ∀ j, 0 ≤ Meta j
  samples :
    let F := actualOriginalOpenParameterSlice Data baseIndex
    let host := fun nu a => (piece nu a).host
    let b := fun nu a => (piece nu a).native
    let g0 := actualOriginalPrimaryFamily Data hd hs hn baseIndex host b
      (fun nu a => (piece nu a).slices) (fun nu a => (piece nu a).data)
      (fun nu a => (piece nu a).cutoff) (fun nu a => (piece nu a).active)
    ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ (G : Set (Ep × M)), IsOpen G → G ⊆ parameterDomain ×ˢ (univ : Set M) →
      ParameterRound2IdentityRefinementSamples Data baseIndex.2 F g0 host b G ell Tinv Forward Meta Rsub Data.primaryCount

variable [T2Space M]

theorem round3_actual_reference_primary_packet
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart baseIndex.2 = OpenPartialHomeomorph.refl Ep)
    (B0 Ts : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B0 j) (hTs : ∀ j, 0 ≤ Ts j) (degree : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas B0 Ts degree)
    (centers : Fin Data.atlas.count → D) (radius : ℝ)
    (hBound : ∀ i, (Data.atlas.chart i) '' Data.atlas.inner i ⊆ closedBall (centers i) radius) :
    ∃ s : Fin Data.primaryCount → Fin Data.atlas.count → Finset X,
      Nonempty (Round3PreparedReferencePrimaryPacket Data hd hs hn baseIndex
        (Sigma (fun nu : Fin Data.primaryCount => Sigma (fun host : Fin Data.atlas.count => ↥(s nu host))))
        ((degree+1)*5^Module.finrank ℝ X)) := by
  obtain ⟨V,hV,hKV,hVO,s,cF,cT,Bnative,piece,hcF,hcT,hB,hBsame,hInner,hGerm,hCount,hFirst,hTransverse⟩ :=
    round3_actual_original_primary_conditioned_preparation Data hd hs hp hImm baseIndex hId
      B0 Ts hB0 hTs degree RS centers radius hBound
  let Β := Sigma (fun nu : Fin Data.primaryCount => Sigma (fun host : Fin Data.atlas.count => ↥(s nu host)))
  let F0 := actualOriginalOpenParameterSlice Data baseIndex
  have hF0joint : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞
      (Function.uncurry F0) (Data.parameterOpen ×ˢ (univ : Set M)) := by
    apply hs.F_joint.congr
    intro z hz
    change actualOriginalOpenParameterSlice Data baseIndex z.1 z.2 = Data.F z
    have hpz : (Data.parameterChart baseIndex.2).symm z.1 ∈ Data.parameterOpen := by
      simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq] using hz.1
    rw [actualOriginalOpenParameterSlice_eq Data baseIndex z.1 hpz]
    simp only [actualOriginalParameterSlice,hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq]
  have hLocal (nu : Fin Data.primaryCount) (a : Β) :=
    round3_prepared_primary_reference_target_profiled Data hd baseIndex.2 nu
      (Data.parameterOpen ×ˢ (univ : Set M)) (piece nu a) (hInner nu a) F0 hF0joint
  choose MHlocal out TiAll TfAll hMHlocal hHost hCut hb hbi hSlices hTarget hBNative hHessian
    hTiAll hTfAll hAllInv hAllForw hInnerSource using hLocal
  let MH := round3PreparedFiniteMaximum (fun a : Fin Data.primaryCount × Β => MHlocal a.1 a.2)
  have hMH : 0 ≤ MH := round3PreparedFiniteMaximum_nonneg _
  have hInner' : ∀ nu (a : Β) y, y ∈ tsupport (out nu a).cutoff → y.2 ∈ Data.atlas.inner (out nu a).host := by
    intro nu a y hy
    rw [hHost]
    exact hInner nu a y (by rwa [hCut] at hy)
  have hCount' : ∀ nu y, (Finset.univ.filter (fun a : Β => y ∈ tsupport (out nu a).cutoff)).card ≤
      (degree+1)*5^Module.finrank ℝ X := by
    intro nu y
    simpa only [hCut] using hCount nu y
  let Tchart := fun j => round3PreparedFiniteMaximum
    (fun a : Fin Data.primaryCount × Β => TiAll a.1 a.2 j)
  let Tforward := fun j => round3PreparedFiniteMaximum
    (fun a : Fin Data.primaryCount × Β => TfAll a.1 a.2 j)
  obtain ⟨Ti,Tf,Te,hTi,hTf,hTe,hSamples⟩ := round3_prepared_primary_original_refinement_samples
    Data hd hs hn baseIndex (Data.parameterOpen ×ˢ (univ : Set M)) out hInner'
    ((degree+1)*5^Module.finrank ℝ X) hCount'
  refine ⟨s,⟨{
    parameterDomain := V
    parameter_open := hV
    parameter_contains := hKV
    parameter_subset := hVO
    piece := out
    cF := cF
    cT := cT
    MH := MH
    Bnative := Bnative
    cF_pos := hcF
    cT_pos := hcT
    MH_nonneg := hMH
    Bnative_pos := hB
    native_bound := fun nu a => (hBNative nu a).trans (hBsame nu a)
    inner := hInner'
    source_inner := hInnerSource
    first := ?_
    transverse := ?_
    hessian := ?_
    Tchart := Tchart
    Tchart_nonneg := fun j => round3PreparedFiniteMaximum_nonneg _
    Tforward := Tforward
    Tforward_nonneg := fun j => round3PreparedFiniteMaximum_nonneg _
    chart_jets_target := ?_
    forward_jets_source := ?_
    chart_jets := ?_
    Tinv := Ti
    Forward := Tf
    Meta := Te
    Tinv_nonneg := hTi
    Forward_nonneg := hTf
    Meta_nonneg := hTe
    samples := ?_ }⟩⟩
  · intro nu a z hz v
    rw [hSlices]
    exact hFirst nu a z (hTarget nu a hz) v
  · intro nu a z hz v
    rw [hSlices]
    exact hTransverse nu a z (hTarget nu a hz) v
  · intro nu a z hz
    exact (hHessian nu a z hz).trans
      (round3PreparedFiniteMaximum_bound (fun a : Fin Data.primaryCount × Β => MHlocal a.1 a.2) (nu,a))
  · intro nu a j z hz
    exact (hAllInv nu a j z hz).trans (round3PreparedFiniteMaximum_bound
      (fun a : Fin Data.primaryCount × Β => TiAll a.1 a.2 j) (nu,a))
  · intro nu a j z hz
    exact (hAllForw nu a j z hz).trans (round3PreparedFiniteMaximum_bound
      (fun a : Fin Data.primaryCount × Β => TfAll a.1 a.2 j) (nu,a))
  · intro nu a j y hy
    have hz : actualHostAdaptedChart (Data.atlas.chart (out nu a).host) (out nu a).native y ∈ (out nu a).native.target := by
      rw [← (out nu a).data.1]
      exact (actualHostAdaptedChart (Data.atlas.chart (out nu a).host) (out nu a).native).map_source ((out nu a).support hy)
    exact (hAllInv nu a j _ hz).trans (round3PreparedFiniteMaximum_bound
      (fun a : Fin Data.primaryCount × Β => TiAll a.1 a.2 j) (nu,a))
  · intro F host b g0 ell hell hell1 G hG hGV
    apply hSamples ell hell hell1 G hG
    · intro nu y hy
      have hh := hGerm nu y (parameterRound2_relativeSupport_mono_open (V ×ˢ (univ : Set M)) G
        (hV.prod isOpen_univ) hG hGV _ hy)
      simpa only [hCut] using hh
    · intro y hy
      exact (Finset.card_filter_le _ _).trans_eq (by simp)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_actual_reference_primary_packet
