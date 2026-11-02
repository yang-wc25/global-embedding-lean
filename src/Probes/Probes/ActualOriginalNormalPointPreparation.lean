import Probes.ActualOriginalFreeNormalField
import Probes.ActualOriginalFreeNormalStability

/-! Pointwise unit length and beta freedom for the literal normalized
two-projection field of the actual map. This separates finite-dimensional
normalization algebra from the quantitative reference-field preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance prepFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance prepFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance prepHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance prepHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance prepFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance prepFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

private theorem normalized_projection_properties
    {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
    (A : E →L[ℝ] V) (B : T →L[ℝ] V) (v : V)
    (hRange : LinearMap.range B.toLinearMap ≤ (LinearMap.range A.toLinearMap)ᗮ)
    (hn : actualFreeNormalProjectionRaw A B v ≠ 0) :
    ‖NormedSpace.normalize (actualFreeNormalProjectionRaw A B v)‖ = 1 ∧
    NormedSpace.normalize (actualFreeNormalProjectionRaw A B v) ∈ (LinearMap.range A.toLinearMap)ᗮ ∧
    NormedSpace.normalize (actualFreeNormalProjectionRaw A B v) ∈ (LinearMap.range B.toLinearMap)ᗮ := by
  obtain ⟨hA,hB⟩ := actual_free_normal_projection_mem A B v hRange
  exact ⟨NormedSpace.norm_normalize hn,
    (LinearMap.range A.toLinearMap)ᗮ.smul_mem _ hA,
    (LinearMap.range B.toLinearMap)ᗮ.smul_mem _ hB⟩

omit [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] in
theorem actual_original_unit_free_normal_field_beta_at
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (v0 : X → V) (z : X) (hx : z.2 ∈ (e z.1).target)
    (hnonzero : actualOriginalFreeNormalFieldRaw F hF e v0 z ≠ 0) :
    ∃ normal : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2),
      (normal : V) = actualOriginalUnitFreeNormalField F hF e v0 z ∧ ‖normal‖ = 1 ∧
      incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ) normal = 0 := by
  let A := fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  let B := incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2
  have hRange : LinearMap.range B.toLinearMap ≤ (LinearMap.range A.toLinearMap)ᗮ := by
    rintro w ⟨t,rfl⟩
    rw [← actual_increment_normalSpace_eq_chart_range (F z.1) (hF z.1)
      (e z.1) (he z.1) z.2 hx]
    change incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 t ∈ _
    rw [incrementsModeAmbientTransverseFrame_eq]
    exact ((incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ)).adjoint t).property
  have hRawNonzero : actualFreeNormalProjectionRaw A B (v0 z) ≠ 0 := hnonzero
  obtain ⟨hUnit,hNormal,hTransverse⟩ := normalized_projection_properties A B (v0 z) hRange hRawNonzero
  have hn : actualOriginalUnitFreeNormalField F hF e v0 z ∈
      normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2) := by
    rw [actual_increment_normalSpace_eq_chart_range (F z.1) (hF z.1) (e z.1) (he z.1)
      z.2 hx]
    exact hNormal
  let normal : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2) := ⟨_,hn⟩
  have hb := actual_original_normal_beta_of_frame_orthogonal (F z.1) (hF z.1)
    (e z.1).symm z.2 normal hTransverse
  exact ⟨normal,rfl,hUnit,hb⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_unit_free_normal_field_beta_at
