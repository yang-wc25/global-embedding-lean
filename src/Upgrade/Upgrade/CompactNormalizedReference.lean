import Upgrade.CompactFixedAtlasSupportedGeometry
import Upgrade.CompactPrincipalNeighborhood

/-!
# The actual normalized reference form before finite cover selection

This field is built from the reference immersion's actual projected coordinate
Hessian and one fixed inverse atlas frame. Its value at the packet center is
the native actual second form. Its continuity supplies an honest spatial
neighborhood for the Schur block or supported defining chart before probes.
-/

noncomputable section
open Set Filter Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

def normalizedReferenceForm
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (z : M) : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F x :=
  (fixedAtlasNormalForm A F F x i z).comp (probeAtlasNormalizationSquare A hA i x hx)

theorem normalizedReferenceForm_self
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) :
    normalizedReferenceForm A hA F i x hx x =
      LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x) := by
  have hself := fixedAtlasNormalForm_self A hA F hF i x hx
  let e := probeAtlasInverseFrameEquiv A hA i x hx
  let B : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x := trueSecondForm F hF x
  apply ContinuousLinearMap.ext
  intro q
  have h := congrArg (fun L : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x ↦
    L (symmetricSquareLinearMap e.symm.toLinearMap q)) hself
  change fixedAtlasNormalForm A F F x i x (symmetricSquareLinearMap e.symm.toLinearMap q) =
    B (symmetricSquareLinearMap e.toLinearMap (symmetricSquareLinearMap e.symm.toLinearMap q)) at h
  change fixedAtlasNormalForm A F F x i x (symmetricSquareLinearMap e.symm.toLinearMap q) = B q
  rw [h]
  have he : symmetricSquareLinearMap e.toLinearMap
      (symmetricSquareLinearMap e.symm.toLinearMap q) = q := by
    have he₁ : symmetricSquareLinearMap e.toLinearMap = symmetricSquareMap e.toContinuousLinearMap :=
      symmetric_square_linear_map_eq e.toContinuousLinearMap
    have he₂ : symmetricSquareLinearMap e.symm.toLinearMap =
        symmetricSquareMap e.symm.toContinuousLinearMap :=
      symmetric_square_linear_map_eq e.symm.toContinuousLinearMap
    rw [he₁, he₂, symmetricSquareMap_comp]
    have hc : e.toContinuousLinearMap.comp e.symm.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ E := by
      apply ContinuousLinearMap.ext
      intro v
      exact e.apply_symm_apply v
    rw [hc, symmetricSquareMap_id]
  exact congrArg B he

theorem continuousAt_normalizedReferenceForm [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) :
    ContinuousAt (normalizedReferenceForm A hA F i x hx) x := by
  have hS := ((continuousOn_probeAtlasProjectedSecondForm A hA F hF himm i) x hx).continuousAt
    ((A.chart i).open_source.mem_nhds hx)
  exact (continuousAt_const.clm_comp hS).clm_comp continuousAt_const

private theorem eventually_norm_sub_lt
    {X Y : Type*} [TopologicalSpace X] [SeminormedAddCommGroup Y]
    {f : X → Y} {x : X} (hf : ContinuousAt f x) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ z in 𝓝 x, ‖f z - f x‖ < r := by
  exact (hf.sub continuousAt_const).norm.eventually_lt_const (by
    change ‖f x - f x‖ < r
    simpa only [sub_self, norm_zero] using hr)

/-- One fixed source neighborhood simultaneously keeps the actual old form
inside a requested chart radius and the old normal target coordinate injective.
No normal identification of a perturbed family is assumed. -/
theorem exists_normalizedReference_neighborhood [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (i : Fin A.count) (x : M) (hx : x ∈ interior (A.support i))
    {delta : ℝ} (hdelta : 0 < delta) :
    let hxc := hA.support_subset i (interior_subset hx)
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ interior (A.support i) ∧
      (∀ z ∈ U, ‖normalizedReferenceForm A hA F i x hxc z -
        LinearMap.toContinuousLinearMap
          (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x)‖ < delta) ∧
      (∀ z ∈ U, ‖(normalSpace (I := IM) F z).starProjection -
        (normalSpace (I := IM) F x).starProjection‖ < 1 / 2) := by
  intro hxc
  have hC := continuousAt_normalizedReferenceForm A hA F hF himm i x hxc
  have hCn : ∀ᶠ z in 𝓝 x,
      ‖normalizedReferenceForm A hA F i x hxc z -
        normalizedReferenceForm A hA F i x hxc x‖ < delta := by
    exact @eventually_norm_sub_lt M (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F x)
      _ ContinuousLinearMap.toSeminormedAddCommGroup _ x hC delta hdelta
  rw [normalizedReferenceForm_self A hA F hF i x hxc] at hCn
  have hP := (smooth_immersion_normal_projection F hF himm).continuous.continuousAt (x := x)
  have hPn : ∀ᶠ z in 𝓝 x, ‖(normalSpace (I := IM) F z).starProjection -
      (normalSpace (I := IM) F x).starProjection‖ < (1 / 2 : ℝ) := by
    exact eventually_norm_sub_lt hP (by norm_num)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp
    (hCn.and (hPn.and (isOpen_interior.mem_nhds hx)))
  exact ⟨U, hU, hxU, fun z hz ↦ (hUsub hz).2.2,
    fun z hz ↦ (hUsub hz).1, fun z hz ↦ (hUsub hz).2.1⟩

end GlobalEmbedding.Upgrade
