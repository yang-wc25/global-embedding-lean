import Probes.ActualSecondaryNativeTensorNorm

/-! Exact native tensor algebra and the unchanged source-first coordinate map.
These identities retain the SAME functions, parameter inverses and source tangent
vectors. They are used to add the actual finite mean residual after estimating
the three non-mean metric terms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold
open scoped ContDiff ENNReal
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
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

 theorem actual_original_native_tensor_sub
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (T S : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (i : Fin A.count × Fin pcount) (z : X) :
    actualOriginalNativeTargetTensor A B (fun p x => T p x-S p x) i z =
      actualOriginalNativeTargetTensor A B T i z-actualOriginalNativeTargetTensor A B S i z := by
  apply actual_bilinear_tensor_eq_of_basis
  intro a b
  simp only [actualOriginalNativeTargetTensor_basis,sub_apply,LinearMap.sub_apply]

 theorem actual_original_native_tensor_smul
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) (r : ℝ)
    (i : Fin A.count × Fin pcount) (z : X) :
    actualOriginalNativeTargetTensor A B (fun p x => r • T p x) i z =
      r • actualOriginalNativeTargetTensor A B T i z := by
  apply actual_bilinear_tensor_eq_of_basis
  intro a b
  simp only [actualOriginalNativeTargetTensor_basis,smul_apply,LinearMap.smul_apply,smul_eq_mul]

 theorem actual_original_native_metric_error_pullback
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (F U : P × M → V)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => F (p,x)))
    (hU : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => U (p,x)))
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
  have hright := actual_original_metric_error_coordinates A B hA F U hF hU H delta i (a z) hy
  have heq := hleft.symm.trans hright
  change parameterRound2_metricComponents (m+1)
    (actualOriginalNativeTargetTensor A B (incrementsOriginalMetricError F U H delta) i (a.symm (a z))) =
      parameterRound2_metricComponents (m+1) (actualOriginalNativeMetricError A B F U H delta i (a.symm (a z))) at heq
  rw [a.symm_apply_apply] at heq
  apply actual_bilinear_tensor_eq_of_basis
  intro r s
  simpa only [parameterRound2_metricComponents_apply,Equiv.symm_apply_apply] using
    congrFun heq (finProdFinEquiv (r,s))

 theorem actual_original_tensor_coordinates_smooth_of_native
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hT : ∀ i, ContDiffOn ℝ ∞ (actualOriginalNativeTargetTensor A B T i)
      ((B i.2).target ×ˢ (A.chart i.1).target)) :
    ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B T i)
      (incrementsOriginalDifferentiation A B i) := by
  intro i
  let a := parameterTensorModelEquiv (m+1) d
  have hmap : MapsTo a.symm (incrementsOriginalDifferentiation A B i)
      ((B i.2).target ×ˢ (A.chart i.1).target) := fun y hy => ⟨hy.2,hy.1⟩
  have hh := ((parameterRound2_metricComponents (m+1)).contDiff.comp_contDiffOn (hT i)).comp
    a.symm.contDiff.contDiffOn hmap
  exact hh.congr (fun y _ => actual_original_tensor_coordinates_native A B T i y)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_native_metric_error_pullback
#print axioms GlobalEmbedding.Continuation.actual_original_tensor_coordinates_smooth_of_native
