import Probes.Round3PreparedOpenReserve
import Probes.ActualOriginalFreeNormalStability
import Probes.ActualIncrementHostGeometryInputs
import Probes.ActualOriginalChartImmersion

/-! Pointwise true new-map reserves on the active carrier become a genuine
open adapted target. The numerical losses are the fixed factors four and
two. The first-frame neighborhood is made before using smooth normal
projection, so no immersion of the perturbed map is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)
private local instance stableFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance stableFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance stableHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance stableHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance stableFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance stableFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem round3_prepared_actual_stable_frames
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) b.target)
    (K : Set X) (hKt : K ⊆ b.target)
    (cF cT : ℝ) (hcF : 0 < cF) (hcT : 0 < cT)
    (hFirst : ∀ z ∈ K, ∀ v : D, cF*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hFrame : ∀ z ∈ K, ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2) :
    ∃ O : Set X, IsOpen O ∧ K ⊆ O ∧ O ⊆ b.target ∧
      (∀ z ∈ O, ∀ v : D, (cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2) ∧
      (∀ z ∈ O, ∀ v : Tdata, (cT/4)*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2) ∧
      ∀ z ∈ O, Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) ((e z.1).symm z.2)) := by
  let A := fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  let H := fun z : X => fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2
  let B := fun z : X => incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2
  have hg := actual_host_slice_geometry_inputs c hc b psi e hdata
  have he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M := hdata.2.2.2.2.1
  have hA : ContDiffOn ℝ ∞ A b.target :=
    (incrementsJointSpatialJets_bridge _ b.target b.open_target hJoint).2.1
  have hH : ContDiffOn ℝ ∞ H b.target :=
    (incrementsJointSpatialJets_bridge _ b.target b.open_target hJoint).2.2
  obtain ⟨UF,hUF,hKUF,hUFt,hAF⟩ := round3_prepared_fixed_reserve_open A b.target K
    b.open_target hKt hA.continuousOn cF hcF hFirst
  have hAi (z : X) (hz : z ∈ UF) : Function.Injective (A z) :=
    actual_first_frame_injective_of_reserve (A z) (cF/4) (by positivity) (hAF z hz)
  have hPA : ContDiffOn ℝ ∞ (fun z : X => (LinearMap.range (A z).toLinearMap)ᗮ.starProjection) UF :=
    smooth_frame_normal_projection A (hA.mono hUFt) hAi
  have hB : ContDiffOn ℝ ∞ B UF := by
    have hColumns : ContDiffOn ℝ ∞ (fun z : X => actualIncrementTransverseColumns m N (H z)) UF :=
      (actualIncrementTransverseColumns m N).contDiff.comp_contDiffOn (hH.mono hUFt)
    apply (hPA.clm_comp hColumns).congr
    intro z hz
    exact actual_original_transverse_frame_projected_columns (F z.1) (hF z.1) (e z.1) (he z.1)
      z.2 (hg.2.2.2.1 z (hUFt hz)).1
  obtain ⟨UT,hUT,hKUT,hUTF,hBT⟩ := round3_prepared_fixed_reserve_open B UF K
    hUF hKUF hB.continuousOn cT hcT hFrame
  refine ⟨UT,hUT,hKUT,hUTF.trans hUFt,
    fun z hz => hAF z (hUTF hz),hBT,?_⟩
  intro z hz
  exact actual_increment_immersion_of_chart_reserve (F z.1) (hF z.1) (e z.1) (he z.1) z.2
    (hg.2.2.2.1 z (hUFt (hUTF hz))).1 (cF/4) (by positivity) (hAF z (hUTF hz))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_actual_stable_frames
