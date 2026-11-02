import NormalPolar.ActualRepairParameterCutoff

/-! A parameter chart with a genuinely global smooth forward coordinate
map. We choose a new legal restricted chart inside an original smooth
chart; its source and target are explicitly stated. On that source the
forward map is exactly the old chart, while its outside extension is the
constructed cutoff coordinate. This prepares finite transition bounds on
the whole compact physical parameter manifold without assuming bounds near
another chart's open-source boundary. -/

noncomputable section
open Set Function Manifold IsManifold Metric
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar

variable {d : ℕ} {P : Type*} [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem passiveOriginalParameterCutoff_eq
    (e : OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (f : ContDiffBump c)
    (p : P) (hp : p ∈ e.source)
    (hc : e p ∈ closedBall c f.rIn) :
    c + actualParameterChartCutoff e c f p = e p := by
  simp only [actualParameterChartCutoff,if_pos hp,f.one_of_mem_closedBall hc,one_smul]
  abel

/-- A new legal restricted parameter chart with the explicit global
cutoff extension. Neither the original source atlas nor its norm is altered. -/
def passiveOriginalGlobalParameterChart
    (e : OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (f : ContDiffBump c)
    (hball : closedBall c f.rOut ⊆ e.target) :
    OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)) where
  toFun p := c + actualParameterChartCutoff e c f p
  invFun := e.symm
  source := e.source ∩ e ⁻¹' ball c f.rIn
  target := ball c f.rIn
  map_source' := by
    intro p hp
    rw [passiveOriginalParameterCutoff_eq e c f p hp.1 (ball_subset_closedBall hp.2)]
    exact hp.2
  map_target' := by
    intro y hy
    have ht : y ∈ e.target := hball
      (closedBall_subset_closedBall f.rIn_lt_rOut.le (ball_subset_closedBall hy))
    exact ⟨e.map_target ht,by simpa only [mem_preimage,e.right_inv ht] using hy⟩
  left_inv' := by
    intro p hp
    rw [passiveOriginalParameterCutoff_eq e c f p hp.1 (ball_subset_closedBall hp.2)]
    exact e.left_inv hp.1
  right_inv' := by
    intro y hy
    have ht : y ∈ e.target := hball
      (closedBall_subset_closedBall f.rIn_lt_rOut.le (ball_subset_closedBall hy))
    rw [passiveOriginalParameterCutoff_eq e c f (e.symm y) (e.map_target ht)]
    · exact e.right_inv ht
    · simpa only [e.right_inv ht] using ball_subset_closedBall hy
  continuousOn_toFun := by
    apply (e.continuousOn.mono inter_subset_left).congr
    intro p hp
    exact passiveOriginalParameterCutoff_eq e c f p hp.1 (ball_subset_closedBall hp.2)
  continuousOn_invFun := e.continuousOn_symm.mono
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall f.rIn_lt_rOut.le)).trans hball)
  open_source := e.isOpen_inter_preimage isOpen_ball
  open_target := isOpen_ball

@[simp] theorem passiveOriginalGlobalParameterChart_source
    (e : OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (f : ContDiffBump c)
    (hball : closedBall c f.rOut ⊆ e.target) :
    (passiveOriginalGlobalParameterChart e c f hball).source =
      e.source ∩ e ⁻¹' ball c f.rIn := rfl

@[simp] theorem passiveOriginalGlobalParameterChart_target
    (e : OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (f : ContDiffBump c)
    (hball : closedBall c f.rOut ⊆ e.target) :
    (passiveOriginalGlobalParameterChart e c f hball).target = ball c f.rIn := rfl

theorem passiveOriginalGlobalParameterChart_smooth
    (e : OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ maximalAtlas 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P)
    (c : EuclideanSpace ℝ (Fin d)) (f : ContDiffBump c)
    (hball : closedBall c f.rOut ⊆ e.target) :
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞
      (passiveOriginalGlobalParameterChart e c f hball) :=
  contMDiff_const.add (actualParameterChartCutoff_smooth e he c f hball)

theorem passiveOriginalGlobalParameterChart_mem_maximalAtlas
    (e : OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (he : e ∈ maximalAtlas 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P)
    (c : EuclideanSpace ℝ (Fin d)) (f : ContDiffBump c)
    (hball : closedBall c f.rOut ⊆ e.target) :
    passiveOriginalGlobalParameterChart e c f hball ∈
      maximalAtlas 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P := by
  let U := e.source ∩ e ⁻¹' ball c f.rIn
  have hU : IsOpen U := e.isOpen_inter_preimage isOpen_ball
  have hrestrict : e.restr U ∈ maximalAtlas 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ 𝓘(ℝ,EuclideanSpace ℝ (Fin d))) he hU
  apply (contDiffGroupoid ∞ 𝓘(ℝ,EuclideanSpace ℝ (Fin d))).mem_maximalAtlas_of_eqOnSource
    (e := e.restr U) _ hrestrict
  refine ⟨?_,?_⟩
  · change U = e.source ∩ interior U
    rw [hU.interior_eq]
    exact (inter_eq_right.mpr inter_subset_left).symm
  · intro p hp
    exact passiveOriginalParameterCutoff_eq e c f p hp.1 (ball_subset_closedBall hp.2)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginalGlobalParameterChart
#print axioms GlobalEmbedding.Continuation.passiveOriginalGlobalParameterChart_smooth
#print axioms GlobalEmbedding.Continuation.passiveOriginalGlobalParameterChart_mem_maximalAtlas
