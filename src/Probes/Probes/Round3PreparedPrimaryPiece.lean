import Probes.Round3PreparedPrimaryRefinement

/-! Genuine primary host pieces. The inhabited producer below is the actual
compact refinement from original smooth phases; empty pieces are used only
for zero padding of finite dependent index families. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
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

structure Round3PreparedPrimaryPiece
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M)) where
  host : Fin Data.atlas.count
  native : OpenPartialHomeomorph X X
  slices : Ep → OpenPartialHomeomorph M D
  cutoff : Ep × M → ℝ
  data : ActualOriginalHostSliceData (Data.atlas.chart host) native
    (fun z : Ep × M => Data.phase nu ((Data.parameterChart ip).symm z.1,z.2)) slices
  native_source : native.source ⊆ actualOriginalNativeOpen Data (host,ip)
  source_domain : (actualHostAdaptedChart (Data.atlas.chart host) native).source ⊆ W
  active : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart host) native).source,
    ((Data.parameterChart ip).symm w.1,w.2) ∈
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data
  compact : IsCompact (tsupport cutoff)
  smooth : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ cutoff
  support : tsupport cutoff ⊆ (actualHostAdaptedChart (Data.atlas.chart host) native).source
  Bnative : ℝ
  positive : 0 < Bnative
  native_first : ∀ z ∈ native.source, ‖fderiv ℝ native z‖ ≤ Bnative

def round3PreparedEmptyNativeChart : OpenPartialHomeomorph X X :=
  (OpenPartialHomeomorph.refl X).restrOpen ∅ isOpen_empty

@[simp] theorem round3PreparedEmptyNativeChart_source :
    (round3PreparedEmptyNativeChart (m := m) (d := d)).source = ∅ := by
  change (univ : Set X) ∩ ∅ = ∅
  exact inter_empty _

@[simp] theorem round3PreparedEmptyNativeChart_target :
    (round3PreparedEmptyNativeChart (m := m) (d := d)).target = ∅ := by
  change (univ : Set X) ∩ (id : X → X) ⁻¹' ∅ = ∅
  simp only [preimage_empty,inter_empty]

def round3PreparedPrimaryEmpty
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (nu : Fin Data.primaryCount) (W : Set (Ep × M)) :
    Round3PreparedPrimaryPiece Data baseIndex.2 nu W := by
  let b := round3PreparedEmptyNativeChart (m := m) (d := d)
  let c := Data.atlas.chart baseIndex.1
  let psi := fun z : Ep × M => Data.phase nu ((Data.parameterChart baseIndex.2).symm z.1,z.2)
  have hbS : b.source = ∅ := round3PreparedEmptyNativeChart_source
  have hbT : b.target = ∅ := round3PreparedEmptyNativeChart_target
  have hsource : b.source ⊆ (actualOriginalHostJointChart («Ep» := Ep) c).target := by
    rw [hbS]; exact empty_subset _
  obtain ⟨hat,ha,hai,hforw,hex⟩ := actual_adapted_chart_original_host c
    (hd.atlas_smooth.chart_mem baseIndex.1) psi b hsource
    (by rw [hbS]; exact contDiffOn_empty) (by rw [hbT]; exact contDiffOn_empty)
    (fun z hz => (hbS ▸ hz : z ∈ (∅ : Set X)).elim)
    (fun z hz => (hbS ▸ hz : z ∈ (∅ : Set X)).elim)
  let e := Classical.choose hex
  have he := Classical.choose_spec hex
  have haS : (actualHostAdaptedChart c b).source = ∅ := by
    simp only [actualHostAdaptedChart,OpenPartialHomeomorph.trans_source,hbS,preimage_empty,inter_empty]
  exact {
    host := baseIndex.1
    native := b
    slices := e
    cutoff := 0
    data := ⟨hat,ha,hai,hforw,he⟩
    native_source := by rw [hbS]; exact empty_subset _
    source_domain := by rw [haS]; exact empty_subset _
    active := by intro w hw; exact (haS ▸ hw : w ∈ (∅ : Set (Ep × M))).elim
    compact := by simpa only [tsupport_zero] using (isCompact_empty : IsCompact (∅ : Set (Ep × M)))
    smooth := contMDiff_const
    support := by rw [tsupport_zero]; exact empty_subset _
    Bnative := 1
    positive := zero_lt_one
    native_first := by intro z hz; exact (hbS ▸ hz : z ∈ (∅ : Set X)).elim }

@[simp] theorem round3PreparedPrimaryEmpty_cutoff
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (nu : Fin Data.primaryCount) (W : Set (Ep × M)) :
    (round3PreparedPrimaryEmpty Data hd baseIndex nu W).cutoff = 0 := rfl

variable [T2Space M]

theorem round3_actual_original_primary_pieces
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
    ∃ (s : Finset X) (out : s → Round3PreparedPrimaryPiece Data i.2 nu W),
      (∀ a : s, (out a).host = i.1) ∧
      (∀ a : s, tsupport (out a).cutoff ⊆ tsupport theta) ∧
      (∀ y ∈ incrementsGlobalRelativeSupport W
          (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)),
        ∀ᶠ w in 𝓝 y, ∑ a : s, (out a).cutoff w = theta w) ∧
      ∀ y, (Finset.univ.filter (fun a : s => y ∈ tsupport (out a).cutoff)).card ≤ 5^Module.finrank ℝ X := by
  obtain ⟨s,b,e,eta,Bnative,hB,hData,hNative,hSource,hActive,hCompactEta,hSmooth,hSupport,hSum,hGerm,hCount,hFirst⟩ :=
    round3_actual_original_primary_refinement Data hd hs hp i nu W hW hParam hOriginal
      theta hCompact hTheta hThetaSupport
  let out := fun a : s => ({
    host := i.1
    native := b a
    slices := e a
    cutoff := eta a
    data := hData a
    native_source := hNative a
    source_domain := hSource a
    active := hActive a
    compact := hCompactEta a
    smooth := hSmooth a
    support := fun _ hz => (hSupport a hz).1
    Bnative := Bnative
    positive := hB
    native_first := hFirst a } : Round3PreparedPrimaryPiece Data i.2 nu W)
  exact ⟨s,out,fun _ => rfl,fun a _ hz => (hSupport a hz).2,hGerm,hCount⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3PreparedPrimaryEmpty
#print axioms GlobalEmbedding.Continuation.round3_actual_original_primary_pieces
