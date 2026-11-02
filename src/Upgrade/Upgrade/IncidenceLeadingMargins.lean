import Upgrade.IncidenceAtlasLeading
import Upgrade.IncidencePairedColumns

/-!
# Neighborhood margins for the same actual finite principal fields

A fixed packet is selected at one actual source point. This file bounds the
variation of its actual tensor/value fields on a neighborhood in the chosen
atlas, and adds that variation to the full paired-response error. Both the
equation-derivative variation and the leading-field variation are retained.
-/

noncomputable section
open Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

variable {W R : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup R] [NormedSpace ℝ R]

/-- Literal principal fields in one fixed source and normal coordinate chart. -/
def atlasIncidencePrincipal
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source)
    (normalProjection : V →L[ℝ] W) (D : (SymmetricSquare E →L[ℝ] W) →L[ℝ] R)
    (weight : ℝ) (z : E) : R × V :=
  (D (normalProjection.comp
      (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx ((A.chart i).symm z))
        (w.tensor ((A.chart i).symm z)))),
    -(weight ^ 2)⁻¹ • w.value ((A.chart i).symm z))

/-- Smoothness of the same actual principal fields, including the source
frame variation. The equation derivative D is fixed at the packet center. -/
theorem atlasIncidencePrincipal_contDiffOn [T2Space M]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source)
    (normalProjection : V →L[ℝ] W) (D : (SymmetricSquare E →L[ℝ] W) →L[ℝ] R)
    (weight : ℝ) :
    ContDiffOn ℝ ∞ (atlasIncidencePrincipal w A hA i x hx normalProjection D weight)
      (A.chart i).target := by
  have hT := w.normalizedAtlasLeadingTensor_contDiffOn A hA i x hx
  have hN := (contDiffOn_const (c := normalProjection)).clm_comp hT
  have hD := D.contDiff.comp_contDiffOn hN
  have hV := (w.atlasLeadingValue_contDiffOn A hA i).const_smul (-(weight ^ 2)⁻¹)
  exact hD.prodMk hV

/-- At the packet center the normalized fields are exactly the original
native packet columns. -/
theorem atlasIncidencePrincipal_at_center
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source)
    (normalProjection : V →L[ℝ] W) (D : (SymmetricSquare E →L[ℝ] W) →L[ℝ] R)
    (weight : ℝ) :
    atlasIncidencePrincipal w A hA i x hx normalProjection D weight (A.chart i x) =
      (D (normalProjection.comp (w.tensor x)), -(weight ^ 2)⁻¹ • w.value x) := by
  unfold atlasIncidencePrincipal
  rw [(A.chart i).left_inv hx, probeTensorInFrame_normalized_self]

/-- One open neighborhood controls every member of the SAME finite actual
packet. This includes empty finite label types. -/
theorem exists_finite_actual_principal_neighborhood [T2Space M]
    {ι : Type*} [Fintype ι]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (waves : ι → LocalLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source)
    (normalProjection : V →L[ℝ] W) (D : (SymmetricSquare E →L[ℝ] W) →L[ℝ] R)
    (weight : ι → ℝ) (eps : ℝ) (heps : 0 < eps) :
    ∃ U : Set E, IsOpen U ∧ A.chart i x ∈ U ∧ U ⊆ (A.chart i).target ∧
      ∀ z ∈ U, ∀ l,
        ‖atlasIncidencePrincipal (waves l) A hA i x hx normalProjection D (weight l) z -
          (D (normalProjection.comp ((waves l).tensor x)),
            -(weight l ^ 2)⁻¹ • (waves l).value x)‖ < eps := by
  have hcenter : A.chart i x ∈ (A.chart i).target := (A.chart i).map_source hx
  have hcont (l : ι) : ContinuousAt
      (atlasIncidencePrincipal (waves l) A hA i x hx normalProjection D (weight l))
      (A.chart i x) :=
    ((atlasIncidencePrincipal_contDiffOn (waves l) A hA i x hx normalProjection D
      (weight l)).continuousOn _ hcenter).continuousAt
        ((A.chart i).open_target.mem_nhds hcenter)
  have hsmall (l : ι) : ∀ᶠ z in 𝓝 (A.chart i x),
      ‖atlasIncidencePrincipal (waves l) A hA i x hx normalProjection D (weight l) z -
        (D (normalProjection.comp ((waves l).tensor x)),
          -(weight l ^ 2)⁻¹ • (waves l).value x)‖ < eps := by
    have h := (hcont l).tendsto.eventually
      (Metric.ball_mem_nhds
        (atlasIncidencePrincipal (waves l) A hA i x hx normalProjection D (weight l)
          (A.chart i x)) heps)
    simpa only [Metric.mem_ball, dist_eq_norm, atlasIncidencePrincipal_at_center] using h
  have hall := (Filter.eventually_all.mpr hsmall).and
    ((A.chart i).open_target.mem_nhds hcenter)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hall
  exact ⟨U, hU, hxU, fun z hz ↦ (hUsub hz).2,
    fun z hz l ↦ (hUsub hz).1 l⟩

section ReferenceError
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The geometric leading-field discrepancy is added to, not discarded from,
the actual normalized paired-incidence error. -/
theorem incidence_error_add_reference_variation
    (actual current reference : S) (rawError geometricError : ℝ)
    (hraw : ‖actual - current‖ ≤ rawError)
    (hgeometry : ‖current - reference‖ ≤ geometricError) :
    ‖actual - reference‖ ≤ rawError + geometricError :=
  (norm_sub_le_norm_sub_add_norm_sub actual current reference).trans (add_le_add hraw hgeometry)

end ReferenceError
end GlobalEmbedding.Upgrade
