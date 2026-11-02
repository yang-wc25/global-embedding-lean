import Probes.ActualIncrementHostGeometryInputs

/-! The true adapted manifold chart derivative is the actual native phase
chart Jacobian composed with the original host derivative. Thus its inverse
kernel norm cost is supplied by original host and constructed-chart bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Filter Bundle
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]

theorem actual_host_slice_forward_derivative
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e)
    (p : Ep) (x : M) (hx : (p,x) ∈ (actualHostAdaptedChart c b).source) :
    (tangentSpaceCastModel 𝓙 (e p x)).toContinuousLinearMap.comp (mfderiv 𝓙 𝓙 (e p) x) =
      (actualJointSpatialJacobian b (p,c x)).comp
        ((tangentSpaceCastModel 𝓙 (c x)).toContinuousLinearMap.comp (mfderiv 𝓙 𝓙 c x)) := by
  have hh := actual_host_slice_geometry_inputs c hc b psi e hdata
  have hd := hdata
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  let g : D → D := fun y => (b (p,y)).2
  have heq : (e p : M → D) = g ∘ c := by
    funext y
    exact hef p y
  have hg : DifferentiableAt ℝ g (c x) := by
    have hs := (hh.2.1.snd.contDiffAt (b.open_source.mem_nhds hx.2)).comp (c x)
      (contDiffAt_const.prodMk contDiffAt_id)
    exact hs.differentiableAt (by simp)
  have hcAt : MDifferentiableAt 𝓙 𝓙 c x :=
    (actual_increment_maximal_chart_mdifferentiable c hc).mdifferentiableAt hx.1.2
  have hcpt := mfderiv_comp x hg.mdifferentiableAt hcAt
  rw [heq]
  rw [mfderiv_eq_fderiv] at hcpt
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L => tangentSpaceCastModel 𝓙 (g (c x)) (L v)) hcpt

private local instance hostForwardDDNormed : NormedAddCommGroup (D →L[ℝ] D) := inferInstance
private local instance hostForwardDDSpace : NormedSpace ℝ (D →L[ℝ] D) := inferInstance
private local instance hostForwardTangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance hostForwardTangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance hostForwardTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance hostForwardTDNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x →L[ℝ] D) := inferInstance
private local instance hostForwardTDSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x →L[ℝ] D) := inferInstance

theorem actual_host_slice_forward_point_norm
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e)
    (hb : ContDiffOn ℝ ∞ b b.source)
    (p : Ep) (x : M) (hx : (p,x) ∈ (actualHostAdaptedChart c b).source)
    (Bhost Bnative : ℝ)
    (hhost : ‖(tangentSpaceCastModel 𝓙 (c x)).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓙 c x)‖ ≤ Bhost)
    (hnative : ‖fderiv ℝ b (p,c x)‖ ≤ Bnative) :
    ‖(tangentSpaceCastModel 𝓙 (e p x)).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓙 (e p) x)‖ ≤ Bnative*Bhost := by
  rw [actual_host_slice_forward_derivative c hc b psi e hdata p x hx]
  let L : D →L[ℝ] D := actualJointSpatialJacobian b (p,c x)
  let C0 : TangentSpace 𝓙 x →L[ℝ] D :=
    (tangentSpaceCastModel 𝓙 (c x)).toContinuousLinearMap.comp (mfderiv 𝓙 𝓙 c x)
  change ‖L.comp C0‖ ≤ Bnative*Bhost
  have hL : ‖L‖ ≤ Bnative :=
    (actual_joint_spatial_jacobian_norm_le b b.source b.open_source hb _ hx.2).trans hnative
  exact (ContinuousLinearMap.opNorm_comp_le L C0).trans
    (mul_le_mul hL hhost C0.opNorm_nonneg (L.opNorm_nonneg.trans hL))


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_host_slice_forward_derivative
#print axioms GlobalEmbedding.Continuation.actual_host_slice_forward_point_norm
