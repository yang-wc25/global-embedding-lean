import Probes.Round3PreparedCompactProfiles
import Probes.ActualOriginalHostTargetRestriction
import GlobalEmbedding.Paper.IncrementsJointSpatialJets
import Mathlib.Topology.MetricSpace.Thickening

/-! A genuine compact effective carrier selects a fixed precompact host
chart, including complete inverse/forward profiles and a reference Hessian
bound. This form applies to actual signed and doubled secondary phases. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance hostFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance hostFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance hostHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] Ey) := inferInstance
private local instance hostHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] Ey) := inferInstance

theorem round3_prepared_reference_host_target
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e)
    (carrier W : Set (Ep × M)) (hCompact : IsCompact carrier)
    (hCarrier : carrier ⊆ (actualHostAdaptedChart c b).source)
    (hSource : (actualHostAdaptedChart c b).source ⊆ W)
    (inner : Set M) (hInnerOpen : IsOpen inner) (hInner : ∀ y ∈ carrier, y.2 ∈ inner)
    (F0 : Ep → M → Ey)
    (hF0 : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F0) W) :
    ∃ (MH : ℝ) (Ti Tf : ℕ → ℝ) (b' : OpenPartialHomeomorph X X)
      (e' : Ep → OpenPartialHomeomorph M D),
      0 ≤ MH ∧ (∀ j, 0 ≤ Ti j) ∧ (∀ j, 0 ≤ Tf j) ∧
      ActualOriginalHostSliceData c b' psi e' ∧ b'.source ⊆ b.source ∧ b'.target ⊆ b.target ∧
      (b' : X → X) = b ∧ (b'.symm : X → X) = b.symm ∧
      (∀ p, ((e' p).symm : D → M) = (e p).symm) ∧
      carrier ⊆ (actualHostAdaptedChart c b').source ∧
      (actualHostAdaptedChart c b').source ⊆ (actualHostAdaptedChart c b).source ∧
      (∀ y ∈ (actualHostAdaptedChart c b').source, y.2 ∈ inner) ∧
      (∀ z ∈ b'.target, ‖fderiv ℝ (fderiv ℝ (F0 z.1 ∘ (e' z.1).symm)) z.2‖ ≤ MH) ∧
      (∀ j z, z ∈ b'.target → ‖iteratedFDeriv ℝ j b'.symm z‖ ≤ Ti j) ∧
      ∀ j z, z ∈ b'.source → ‖iteratedFDeriv ℝ j b' z‖ ≤ Tf j := by
  let a := actualHostAdaptedChart c b
  have hData0 := hdata
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  let K := a '' carrier
  have hK : IsCompact K := hCompact.image_of_continuousOn (a.continuousOn.mono hCarrier)
  let Oinner := a.target ∩ a.symm ⁻¹' ((univ : Set Ep) ×ˢ inner)
  have hOinner : IsOpen Oinner := a.symm.continuousOn.isOpen_inter_preimage a.open_target
    (isOpen_univ.prod hInnerOpen)
  have hKinner : K ⊆ Oinner := by
    rintro _ ⟨y,hy,rfl⟩
    refine ⟨a.map_source (hCarrier hy),?_⟩
    change a.symm (a y) ∈ (univ : Set Ep) ×ˢ inner
    rw [a.left_inv (hCarrier hy)]
    exact ⟨mem_univ _,hInner y hy⟩
  obtain ⟨rho,hrho,hThickInner⟩ := hK.exists_cthickening_subset_open hOinner hKinner
  have hThick : cthickening rho K ⊆ b.target := by
    intro z hz
    rw [← hat]
    exact (hThickInner hz).1
  let O := thickening rho K
  have hO : IsOpen O := isOpen_thickening
  have hKO : K ⊆ O := self_subset_thickening hrho K
  have hOt : O ⊆ b.target := (thickening_subset_cthickening rho K).trans hThick
  have hFjoint : ContDiffOn ℝ ∞ (fun z : X => F0 z.1 ((e z.1).symm z.2)) b.target := by
    have hh := (hF0.comp (hai.mono (by rw [hat]))
      (fun z (hz : z ∈ b.target) => hSource (a.map_target (by rwa [hat])))).contDiffOn
    apply hh.congr
    intro z hz
    change F0 z.1 ((e z.1).symm z.2) = F0 (a.symm z).1 (a.symm z).2
    rw [hpair z hz]
  have hHess : ContinuousOn (fun z : X => fderiv ℝ (fderiv ℝ (F0 z.1 ∘ (e z.1).symm)) z.2) b.target :=
    (incrementsJointSpatialJets_bridge _ b.target b.open_target hFjoint).2.2.continuousOn
  obtain ⟨A,hA0⟩ := (hK.cthickening (r := rho)).exists_bound_of_continuousOn (hHess.norm.mono hThick)
  have hA (z : X) (hz : z ∈ cthickening rho K) :
      ‖fderiv ℝ (fderiv ℝ (F0 z.1 ∘ (e z.1).symm)) z.2‖ ≤ A := by
    simpa only [Real.norm_eq_abs,abs_norm] using hA0 z hz
  obtain ⟨b',e',hTarget,hSrc,hb,hbi,hData,hASource,hSlices⟩ :=
    actual_original_host_restrict_target c hc b psi e hData0 O hO hOt
  have hg := actual_host_slice_geometry_inputs c hc b psi e hData0
  let Ki := cthickening rho K
  have hKi : IsCompact Ki := hK.cthickening
  let Kf := b.symm '' Ki
  have hKf : IsCompact Kf := hKi.image_of_continuousOn (hg.2.2.1.continuousOn.mono hThick)
  have hKfSource : Kf ⊆ b.source := by
    rintro _ ⟨z,hz,rfl⟩
    exact b.map_target (hThick hz)
  obtain ⟨Ti,hTi,hInv⟩ := round3_prepared_compact_profiles b.symm b.target Ki b.open_target hKi hThick hg.2.2.1
  obtain ⟨Tf,hTf,hForw⟩ := round3_prepared_compact_profiles b b.source Kf b.open_source hKf hKfSource hg.2.1
  refine ⟨max 0 A,Ti,Tf,b',e',le_max_left _ _,hTi,hTf,hData,hSrc,?_,hb,hbi,hSlices,?_,?_,?_,?_,?_,?_⟩
  · rw [hTarget]
    exact hOt
  · intro y hy
    rw [hASource]
    exact ⟨hCarrier hy,hKO ⟨y,hy,rfl⟩⟩
  · rw [hASource]
    exact inter_subset_left
  · intro y hy
    rw [hASource] at hy
    have hh := (hThickInner (thickening_subset_cthickening rho K hy.2)).2
    change a.symm (a y) ∈ (univ : Set Ep) ×ˢ inner at hh
    rw [a.left_inv hy.1] at hh
    exact hh.2
  · intro z hz
    rw [hSlices z.1]
    exact (hA z (thickening_subset_cthickening rho K (by rwa [hTarget] at hz))).trans (le_max_right _ _)
  · intro j z hz
    rw [hbi]
    have hh := (hInv 1 (by norm_num) (by norm_num) j z
      (thickening_subset_cthickening rho K (by rwa [hTarget] at hz))).1
    simpa only [one_pow,one_mul] using hh
  · intro j z hz
    rw [hb]
    have hImage : z ∈ Kf := by
      refine ⟨b' z,?_,?_⟩
      · exact thickening_subset_cthickening rho K (by simpa only [hTarget] using b'.map_source hz)
      · rw [← hbi]
        exact b'.left_inv hz
    have hh := (hForw 1 (by norm_num) (by norm_num) j z hImage).1
    simpa only [one_pow,one_mul] using hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_reference_host_target
