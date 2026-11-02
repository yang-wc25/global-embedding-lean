import Repair.EndpointHostTemplateArgument

/-! The tensor tested in the actual Round4 factory is the very same native
tensor pulled into the host used by the original linear coefficient field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation
variable {m d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "IT" => 𝓘(ℝ,D)

theorem repair_host_inverse_at_target
    (host : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas IT ∞ M)
    (y : D) (hy : y ∈ host.target) :
    repairHostInverseDifferential host hhost (host.symm y) (host.map_target hy) =
      actualIncrementChartDerivativeEquiv host hhost y hy := by
  ext v
  apply (actualIncrementChartDerivativeEquiv host hhost y hy).symm.injective
  change (repairHostInverseDifferential host hhost (host.symm y) (host.map_target hy)).symm
      ((repairHostInverseDifferential host hhost (host.symm y) (host.map_target hy)) v) =
    (actualIncrementChartDerivativeEquiv host hhost y hy).symm
      ((actualIncrementChartDerivativeEquiv host hhost y hy) v)
  simp only [ContinuousLinearEquiv.symm_apply_apply]

theorem repair_factory_tensor_at_coordinates
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (i : Fin A.count × Fin c)
    (hhost : A.chart i.1 ∈ IsManifold.maximalAtlas IT ∞ M)
    (z : Ep × D) (hz : z.2 ∈ (A.chart i.1).target) :
    round4OriginalNativeTensorCoordinates A B T i z =
      repairNativeTensorPullback
        (repairHostTensorInverse (A.chart i.1) hhost ((A.chart i.1).symm z.2))
        (T ((B i.2).symm z.1) ((A.chart i.1).symm z.2)) := by
  have hp : incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z) = z.1 :=
    congrArg Prod.fst ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
  have hx : incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z) = z.2 :=
    congrArg Prod.snd ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
  rw [repairHostTensorInverse_on_source _ _ _ ((A.chart i.1).map_target hz),
    repair_host_inverse_at_target _ hhost z.2 hz]
  unfold round4OriginalNativeTensorCoordinates repairNativeTensorPullback
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  apply congrArg (round4NativeTensorFromCoordinates (m+1))
  ext k
  simp only [incrementsOriginalTensorCoordinates, incrementsOriginalJointPoint,
    incrementsOriginalSourceVector, hp, hx, repairNativeTensorEvaluations]
  exact congrArg (fun y : D => T ((B i.2).symm z.1) ((A.chart i.1).symm y)
    (mfderiv IT IT (A.chart i.1).symm y (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
    (mfderiv IT IT (A.chart i.1).symm y (EuclideanSpace.single (finProdFinEquiv.symm k).2 1))) hx

theorem repair_factory_tensor_at_original_point
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (i : Fin A.count × Fin c)
    (hhost : A.chart i.1 ∈ IsManifold.maximalAtlas IT ∞ M)
    (p : P) (hp : p ∈ (B i.2).source) (x : M) (hx : x ∈ (A.chart i.1).source) :
    round4OriginalNativeTensorCoordinates A B T i (B i.2 p,A.chart i.1 x) =
      repairNativeTensorPullback (repairHostTensorInverse (A.chart i.1) hhost x) (T p x) := by
  rw [repair_factory_tensor_at_coordinates A B T i hhost _ ((A.chart i.1).map_source hx)]
  simp only [(B i.2).left_inv hp]
  exact congrArg (fun y : M =>
    repairNativeTensorPullback (repairHostTensorInverse (A.chart i.1) hhost y) (T p y))
    ((A.chart i.1).left_inv hx)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_factory_tensor_at_coordinates
#print axioms GlobalEmbedding.Continuation.repair_factory_tensor_at_original_point
