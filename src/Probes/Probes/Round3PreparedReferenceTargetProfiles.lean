import Probes.Round3PreparedPrimaryPiece
import Probes.Round3PreparedCompactProfiles
import Probes.ActualOriginalHostTargetRestriction
import GlobalEmbedding.Paper.IncrementsJointSpatialJets
import Mathlib.Topology.MetricSpace.Thickening

/-! A fixed primary reference piece is restricted once around its actual
compact support. The reference ordinary Hessian bound is an internal output.
Native chart functions, cutoff and slice inverse functions remain unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance referenceFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance referenceFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance referenceHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance referenceHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance

theorem round3_prepared_primary_reference_target_profiled
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W)
    (hInner : ∀ y, y ∈ tsupport piece.cutoff → y.2 ∈ Data.atlas.inner piece.host)
    (F0 : Ep → M → V)
    (hF0 : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Function.uncurry F0) W) :
    ∃ (MH : ℝ) (out : Round3PreparedPrimaryPiece Data ip nu W) (Tinv Forward : ℕ → ℝ),
      0 ≤ MH ∧ out.host = piece.host ∧ out.cutoff = piece.cutoff ∧
      (out.native : X → X) = piece.native ∧
      (out.native.symm : X → X) = piece.native.symm ∧
      (∀ p, ((out.slices p).symm : D → M) = (piece.slices p).symm) ∧
      out.native.target ⊆ piece.native.target ∧ out.Bnative = piece.Bnative ∧
      (∀ z ∈ out.native.target,
        ‖fderiv ℝ (fderiv ℝ (F0 z.1 ∘ (out.slices z.1).symm)) z.2‖ ≤ MH) ∧
      (∀ j, 0 ≤ Tinv j) ∧ (∀ j, 0 ≤ Forward j) ∧
      (∀ j z, z ∈ out.native.target → ‖iteratedFDeriv ℝ j out.native.symm z‖ ≤ Tinv j) ∧
      (∀ j z, z ∈ out.native.source → ‖iteratedFDeriv ℝ j out.native z‖ ≤ Forward j) ∧
      ∀ y, y ∈ (actualHostAdaptedChart (Data.atlas.chart out.host) out.native).source →
        y.2 ∈ Data.atlas.inner out.host := by
  let c := Data.atlas.chart piece.host
  let b := piece.native
  let a := actualHostAdaptedChart c b
  let psi := fun z : Ep × M => Data.phase nu ((Data.parameterChart ip).symm z.1,z.2)
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  let K := a '' tsupport piece.cutoff
  have hK : IsCompact K := piece.compact.image_of_continuousOn (a.continuousOn.mono piece.support)
  have hKt : K ⊆ b.target := by
    rintro _ ⟨y,hy,rfl⟩
    rw [← hat]
    exact a.map_source (piece.support hy)
  have hFjoint : ContDiffOn ℝ ∞ (fun z : X => F0 z.1 ((piece.slices z.1).symm z.2)) b.target := by
    have hh := (hF0.comp (hai.mono (by rw [hat]))
      (fun z (hz : z ∈ b.target) => piece.source_domain (a.map_target (by rwa [hat])))).contDiffOn
    apply hh.congr
    intro z hz
    change F0 z.1 ((piece.slices z.1).symm z.2) = F0 (a.symm z).1 (a.symm z).2
    rw [hpair z hz]
  have hHess : ContinuousOn
      (fun z : X => fderiv ℝ (fderiv ℝ (F0 z.1 ∘ (piece.slices z.1).symm)) z.2) b.target := by
    exact (incrementsJointSpatialJets_bridge _ b.target b.open_target hFjoint).2.2.continuousOn
  let InnerTarget := a.target ∩ a.symm ⁻¹' ((univ : Set Ep) ×ˢ Data.atlas.inner piece.host)
  have hInnerOpen : IsOpen InnerTarget := a.symm.continuousOn.isOpen_inter_preimage
    a.open_target (isOpen_univ.prod (Data.atlas.inner_open piece.host))
  have hKInner : K ⊆ InnerTarget := by
    rintro _ ⟨y,hy,rfl⟩
    refine ⟨a.map_source (piece.support hy),?_⟩
    change a.symm (a y) ∈ (univ : Set Ep) ×ˢ Data.atlas.inner piece.host
    rw [a.left_inv (piece.support hy)]
    exact ⟨mem_univ _,hInner y hy⟩
  obtain ⟨rho,hrho,hThickInner⟩ := hK.exists_cthickening_subset_open hInnerOpen hKInner
  have hThick : cthickening rho K ⊆ b.target := by
    intro z hz
    rw [← hat]
    exact (hThickInner hz).1
  let O := thickening rho K
  have hO : IsOpen O := isOpen_thickening
  have hKO : K ⊆ O := self_subset_thickening hrho K
  have hOt : O ⊆ b.target := (thickening_subset_cthickening rho K).trans hThick
  obtain ⟨A,hA0⟩ := (hK.cthickening (r := rho)).exists_bound_of_continuousOn (hHess.norm.mono hThick)
  have hA (z : X) (hz : z ∈ cthickening rho K) :
      ‖fderiv ℝ (fderiv ℝ (F0 z.1 ∘ (piece.slices z.1).symm)) z.2‖ ≤ A := by
    simpa only [Real.norm_eq_abs,abs_norm] using hA0 z hz
  obtain ⟨b',e',hTarget,hSource,hb,hbi,hData,hAdaptedSource,hSlices⟩ :=
    actual_original_host_restrict_target c (hd.atlas_smooth.chart_mem piece.host) b psi
      piece.slices piece.data O hO hOt
  have hg := actual_host_slice_geometry_inputs c (hd.atlas_smooth.chart_mem piece.host) b psi piece.slices piece.data
  let Kinv := cthickening rho K
  have hKinv : IsCompact Kinv := hK.cthickening
  let Kforw := b.symm '' Kinv
  have hKforw : IsCompact Kforw := hKinv.image_of_continuousOn (hg.2.2.1.continuousOn.mono hThick)
  have hKforwSource : Kforw ⊆ b.source := by
    rintro _ ⟨z,hz,rfl⟩
    exact b.map_target (hThick hz)
  obtain ⟨Ti,hTi,hInvJets⟩ := round3_prepared_compact_profiles b.symm b.target Kinv
    b.open_target hKinv hThick hg.2.2.1
  obtain ⟨Tf,hTf,hForwJets⟩ := round3_prepared_compact_profiles b b.source Kforw
    b.open_source hKforw hKforwSource hg.2.1
  let out : Round3PreparedPrimaryPiece Data ip nu W := {
    host := piece.host
    native := b'
    slices := e'
    cutoff := piece.cutoff
    data := hData
    native_source := hSource.trans piece.native_source
    source_domain := by rw [hAdaptedSource]; exact inter_subset_left.trans piece.source_domain
    active := by intro w hw; rw [hAdaptedSource] at hw; exact piece.active w hw.1
    compact := piece.compact
    smooth := piece.smooth
    support := by
      intro y hy
      rw [hAdaptedSource]
      exact ⟨piece.support hy,hKO ⟨y,hy,rfl⟩⟩
    Bnative := piece.Bnative
    positive := piece.positive
    native_first := by intro z hz; rw [hb]; exact piece.native_first z (hSource hz) }
  refine ⟨max 0 A,out,Ti,Tf,le_max_left _ _,rfl,rfl,hb,hbi,hSlices,?_,rfl,?_,hTi,hTf,?_,?_,?_⟩
  · change b'.target ⊆ b.target
    rw [hTarget]
    exact hOt
  · intro z hz
    change ‖fderiv ℝ (fderiv ℝ (F0 z.1 ∘ (e' z.1).symm)) z.2‖ ≤ max 0 A
    rw [hSlices z.1]
    exact (hA z (thickening_subset_cthickening rho K (by rwa [hTarget] at hz))).trans (le_max_right _ _)
  · intro j z hz
    change ‖iteratedFDeriv ℝ j b'.symm z‖ ≤ Ti j
    rw [hbi]
    have hh := (hInvJets 1 (by norm_num) (by norm_num) j z
      (thickening_subset_cthickening rho K (by rwa [hTarget] at hz))).1
    simpa only [one_pow,one_mul] using hh
  · intro j z hz
    change ‖iteratedFDeriv ℝ j b' z‖ ≤ Tf j
    rw [hb]
    have hImage : z ∈ Kforw := by
      refine ⟨b' z,?_,?_⟩
      · exact thickening_subset_cthickening rho K (by simpa only [hTarget] using b'.map_source hz)
      · rw [← hbi]
        exact b'.left_inv hz
    have hh := (hForwJets 1 (by norm_num) (by norm_num) j z hImage).1
    simpa only [one_pow,one_mul] using hh
  · intro y hy
    change y ∈ (actualHostAdaptedChart c b').source at hy
    rw [hAdaptedSource] at hy
    have hh := (hThickInner (thickening_subset_cthickening rho K hy.2)).2
    change a.symm (a y) ∈ (univ : Set Ep) ×ˢ Data.atlas.inner piece.host at hh
    rw [a.left_inv hy.1] at hh
    exact hh.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_primary_reference_target_profiled
