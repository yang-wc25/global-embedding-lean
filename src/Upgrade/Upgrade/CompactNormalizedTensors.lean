import Upgrade.CompactNormalizedReference

/-!
# Fixed spatial bounds for actual normalized legal tensors

The tensor fields use the actual varying atlas inverse differential and the
one fixed normalization at their packet center. Their native operator norm is
the original symmetric-square norm. These bounds are selected before returned
probe weights; only the separate raw error will be multiplied by weight
simulation coefficients.
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

private theorem native_norm_neighborhood
    {X Y : Type*} [TopologicalSpace X] [SeminormedAddCommGroup Y]
    {f : X → Y} {x : X} (hf : ContinuousAt f x) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ z in 𝓝 x, ‖f z - f x‖ < r := by
  exact (hf.sub continuousAt_const).norm.eventually_lt_const (by
    change ‖f x - f x‖ < r
    simpa only [sub_self, norm_zero] using hr)

theorem exists_finite_normalized_tensor_neighborhood [T2Space M]
    {ι : Type*} [Fintype ι]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F}
    (waves : ι → LocalLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (i : Fin A.count) (x : M) (hx : x ∈ interior (A.support i))
    {eps : ℝ} (heps : 0 < eps) :
    let hxc := hA.support_subset i (interior_subset hx)
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ interior (A.support i) ∧
      ∀ z ∈ U, ∀ l,
        ‖(normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
            (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hxc z)
              ((waves l).tensor z)) -
          (normalSpace (I := IM) F x).orthogonalProjectionOnto.comp ((waves l).tensor x)‖ < eps := by
  intro hxc
  let T : ι → E → SymmetricSquare E →L[ℝ] normalSpace (I := IM) F x := fun l s ↦
    (normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
      (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hxc ((A.chart i).symm s))
        ((waves l).tensor ((A.chart i).symm s)))
  have hcenter : A.chart i x ∈ (A.chart i).target := (A.chart i).map_source hxc
  have hcont (l : ι) : ContinuousAt (T l) (A.chart i x) := by
    have ht := ((waves l).normalizedAtlasLeadingTensor_contDiffOn A hA i x hxc).continuousOn
    exact (continuousAt_const.clm_comp ((ht _ hcenter).continuousAt
      ((A.chart i).open_target.mem_nhds hcenter)))
  have hsmall (l : ι) : ∀ᶠ s in 𝓝 (A.chart i x),
      ‖T l s - (normalSpace (I := IM) F x).orthogonalProjectionOnto.comp ((waves l).tensor x)‖ < eps := by
    have h := @native_norm_neighborhood E
      (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F x) _
      ContinuousLinearMap.toSeminormedAddCommGroup (T l) (A.chart i x) (hcont l) eps heps
    simpa only [T, (A.chart i).left_inv hxc, probeTensorInFrame_normalized_self] using h
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp (Filter.eventually_all.mpr hsmall)
  let U := ((A.chart i).source ∩ (A.chart i) ⁻¹' W) ∩ interior (A.support i)
  refine ⟨U, ((A.chart i).isOpen_inter_preimage hW).inter isOpen_interior,
    ⟨⟨hxc, hxW⟩, hx⟩, fun _ hz ↦ hz.2, ?_⟩
  intro z hz l
  have h := hWsub hz.1.2 l
  simpa only [T, (A.chart i).left_inv hz.1.1] using h

/-- A finite actual packet has a positive common native tensor bound on a
genuine neighborhood selected before any weights or small-scale response. -/
theorem exists_finite_normalized_tensor_bound [T2Space M]
    {ι : Type*} [Fintype ι]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F}
    (waves : ι → LocalLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (i : Fin A.count) (x : M) (hx : x ∈ interior (A.support i)) :
    let hxc := hA.support_subset i (interior_subset hx)
    ∃ L > 0, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ interior (A.support i) ∧
      ∀ z ∈ U, ∀ l,
        ‖(normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
            (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hxc z)
              ((waves l).tensor z))‖ ≤ L := by
  intro hxc
  obtain ⟨C, hC⟩ := Finite.exists_le (fun l : ι ↦
    ‖(normalSpace (I := IM) F x).orthogonalProjectionOnto.comp ((waves l).tensor x)‖)
  obtain ⟨U, hU, hxU, hUsupport, hT⟩ :=
    exists_finite_normalized_tensor_neighborhood waves A hA i x hx (by norm_num : (0 : ℝ) < 1)
  refine ⟨|C| + 1, by positivity, U, hU, hxU, hUsupport, ?_⟩
  intro z hz l
  have h := norm_le_norm_sub_add
    ((normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
      (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hxc z) ((waves l).tensor z)))
    ((normalSpace (I := IM) F x).orthogonalProjectionOnto.comp ((waves l).tensor x))
  linarith [hT z hz l, hC l, le_abs_self C]

end GlobalEmbedding.Upgrade
