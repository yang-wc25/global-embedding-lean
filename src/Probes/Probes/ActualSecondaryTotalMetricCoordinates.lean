import Probes.ActualSecondaryNativeTensorAlgebra

/-! The native metric-coordinate identity holds for totalized derivatives
through a genuine local diffeomorphism. No global smoothness of a map is
needed to identify its native metric with the coordinate metric. In the
nondifferentiable case both actual derivatives vanish by the inverse germ.
This removes a false global regularity requirement outside the original W. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N pcount : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem actual_ambientDerivative_inverseChart_total
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas 𝓙 ∞ M)
    (f : M → V) (y : D) (hy : y ∈ e.target) (v : D) :
    tangentSpaceCastModel 𝓘(ℝ,V) (f (e.symm y))
      (mfderiv 𝓙 𝓘(ℝ,V) f (e.symm y)
        (mfderiv 𝓘(ℝ,D) 𝓙 e.symm y ((tangentSpaceCastModel 𝓘(ℝ,D) y).symm v))) =
      fderiv ℝ (f ∘ e.symm) y v := by
  have hemd : e.MDifferentiable 𝓙 𝓘(ℝ,D) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  by_cases hf : MDifferentiableAt 𝓙 𝓘(ℝ,V) f (e.symm y)
  · rw [← mfderiv_comp_apply y hf (hemd.mdifferentiableAt_symm hy),mfderiv_eq_fderiv]
    rfl
  · have hn : ¬ DifferentiableAt ℝ (f ∘ e.symm) y := by
      intro h
      have ho : MDifferentiableAt 𝓘(ℝ,D) 𝓘(ℝ,V) (f ∘ e.symm) (e (e.symm y)) := by
        rw [e.right_inv hy]
        exact h.mdifferentiableAt
      have hcomp := ho.comp (e.symm y) (hemd.mdifferentiableAt (e.map_target hy))
      have heq : f =ᶠ[𝓝 (e.symm y)] ((f ∘ e.symm) ∘ e) := by
        filter_upwards [e.open_source.mem_nhds (e.map_target hy)] with x hx
        simp only [Function.comp_apply,e.left_inv hx]
      exact hf (hcomp.congr_of_eventuallyEq heq)
    rw [fderiv_zero_of_not_differentiableAt hn,mfderiv_zero_of_not_mdifferentiableAt hf]
    rfl

 theorem actual_original_metric_error_coordinates_total
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A)
    (F U : P × M → V)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (delta : ℝ) (i : Fin A.count × Fin pcount) (y : Fin (m+1+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i) :
    incrementsOriginalTensorCoordinates A B (incrementsOriginalMetricError F U H delta) i y =
      parameterRound2_metricComponents (m+1)
        (actualOriginalNativeMetricError A B F U H delta i ((parameterTensorModelEquiv (m+1) d).symm y)) := by
  funext k
  let p := (B i.2).symm (incrementsOriginalParameterPoint y)
  let x := incrementsOriginalSourcePoint y
  let v := EuclideanSpace.single (finProdFinEquiv.symm k).1 (1 : ℝ)
  let w := EuclideanSpace.single (finProdFinEquiv.symm k).2 (1 : ℝ)
  have hFv := actual_ambientDerivative_inverseChart_total (A.chart i.1) (hA.chart_mem i.1)
    (fun x => F (p,x)) x hy.1 v
  have hFw := actual_ambientDerivative_inverseChart_total (A.chart i.1) (hA.chart_mem i.1)
    (fun x => F (p,x)) x hy.1 w
  have hSv := actual_ambientDerivative_inverseChart_total (A.chart i.1) (hA.chart_mem i.1)
    (fun x => F (p,x)+U (p,x)) x hy.1 v
  have hSw := actual_ambientDerivative_inverseChart_total (A.chart i.1) (hA.chart_mem i.1)
    (fun x => F (p,x)+U (p,x)) x hy.1 w
  simp only [parameterRound2_metricComponents_apply, actualOriginalNativeMetricError,
    actualFiniteMetricError, sub_apply, smul_apply, smul_eq_mul, actualSpatialMetric_apply,
    actualOriginalNativeTargetTensor_basis]
  exact congrArg (fun t : ℝ => t - delta^2 * H p ((A.chart i.1).symm x)
    (incrementsGlobalObservationVector (I := 𝓙) (A.chart i.1) x (finProdFinEquiv.symm k).1)
    (incrementsGlobalObservationVector (I := 𝓙) (A.chart i.1) x (finProdFinEquiv.symm k).2))
    (congrArg₂ (fun a b : ℝ => a-b)
      (congrArg₂ (fun a b : V => inner ℝ a b) hSv hSw)
      (congrArg₂ (fun a b : V => inner ℝ a b) hFv hFw))

 theorem actual_original_native_metric_error_pullback_total
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (F U : P × M → V)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (delta : ℝ) (i : Fin A.count × Fin pcount) (z : X)
    (hz : z ∈ (B i.2).target ×ˢ (A.chart i.1).target) :
    actualOriginalNativeTargetTensor A B (incrementsOriginalMetricError F U H delta) i z =
      actualOriginalNativeMetricError A B F U H delta i z := by
  let a := parameterTensorModelEquiv (m+1) d
  have hpair : (incrementsOriginalParameterPoint (a z),incrementsOriginalSourcePoint (a z)) = z :=
    a.symm_apply_apply z
  have hpar := congrArg Prod.fst hpair
  have hsrc := congrArg Prod.snd hpair
  have hy : a z ∈ incrementsOriginalDifferentiation A B i := by
    change incrementsOriginalSourcePoint (a z) ∈ (A.chart i.1).target ∧
      incrementsOriginalParameterPoint (a z) ∈ (B i.2).target
    dsimp only at hpar hsrc
    rw [hpar,hsrc]
    exact ⟨hz.2,hz.1⟩
  have hleft := actual_original_tensor_coordinates_native A B (incrementsOriginalMetricError F U H delta) i (a z)
  have hright := actual_original_metric_error_coordinates_total A B hA F U H delta i (a z) hy
  have heq := hleft.symm.trans hright
  change parameterRound2_metricComponents (m+1)
    (actualOriginalNativeTargetTensor A B (incrementsOriginalMetricError F U H delta) i (a.symm (a z))) =
      parameterRound2_metricComponents (m+1) (actualOriginalNativeMetricError A B F U H delta i (a.symm (a z))) at heq
  rw [a.symm_apply_apply] at heq
  apply actual_bilinear_tensor_eq_of_basis
  intro r s
  simpa only [parameterRound2_metricComponents_apply,Equiv.symm_apply_apply] using
    congrFun heq (finProdFinEquiv (r,s))


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_native_metric_error_pullback_total
