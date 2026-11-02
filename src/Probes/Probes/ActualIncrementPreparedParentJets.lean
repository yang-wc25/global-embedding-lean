import Probes.ActualIncrementPreparedSampling
import Smoothing.TensorProductJets
import Smoothing.WeightedActualOperations
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle Filter
open scoped ContDiff Topology BigOperators TensorProduct ENNReal Classical
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance marginSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance marginSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ}
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

variable {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

private local instance adaptedGeometryFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryT0Normed : NormedAddCommGroup (D →L[ℝ] Tdata) := inferInstance
private local instance adaptedGeometryT0Space : NormedSpace ℝ (D →L[ℝ] Tdata) := inferInstance
private local instance marginCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance marginCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance marginCjetNormed : NormedAddCommGroup (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCjetSpace : NormedSpace ℝ (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCANormed : NormedAddCommGroup
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCASpace : NormedSpace ℝ
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace

private local instance rawCoeffInnerNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawCoeffInnerSpace : NormedSpace ℝ
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance rawCoeffOuterNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance rawCoeffOuterSpace : NormedSpace ℝ
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {Β : Type*} [Fintype Β]


/-- The actual smoother's normalized source cutoffs supply every joint
parent-cutoff derivative needed by the adapted refinement. The projection
has norm at most one, including nonzero parameter dimension. -/
theorem actual_uniform_prepared_parent_coordinate_profiles
    (B0 Ts : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B0 j) (hTs : ∀ j, 0 ≤ Ts j) (degree : ℕ) :
    ∃ Bt : ℕ → ℝ, (∀ j, 0 ≤ Bt j) ∧
    ∀ (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
      (RS : TensorRawCutoffPreparation A B0 Ts degree),
    let chi := squareNormalizedCutoff RS.raw
    let theta := fun i (z : Ep × M) => chi i z.2 ^ 2
    (∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i)) ∧
    ∀ i j (ell : ℝ), 0 ≤ ell → ell ≤ 1 → ∀ z : X,
      z.2 ∈ bufferedInnerCoordinates A i → (A.chart i).symm z.2 ∈ tsupport (chi i) →
      ell^j*‖iteratedFDeriv ℝ j (theta i ∘ (actualOriginalHostJointChart («Ep» := Ep) (A.chart i)).symm) z‖ ≤ Bt j := by
  obtain ⟨B,hB,hProduced⟩ := exists_uniform_prepared_tensor_cutoffs
    (E := D) («X» := M) B0 Ts hB0 hTs degree
  let Prefix := fun j => ∑ k ∈ Finset.range (j+1), B k
  have hPrefix : ∀ j, 0 ≤ Prefix j := fun j => Finset.sum_nonneg (fun k hk => hB k)
  let Bt := fun j => 2^j*(‖ContinuousLinearMap.mul ℝ ℝ‖*Prefix j)*Prefix j
  refine ⟨Bt,fun j => mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg (ContinuousLinearMap.mul ℝ ℝ).opNorm_nonneg (hPrefix j))) (hPrefix j),?_⟩
  intro A hA RS chi theta
  obtain ⟨hchi,hpart,hinner,hcount,hbound⟩ := hProduced A hA RS
  refine ⟨(actual_original_prepared_parent_cutoffs (d := d) A B0 Ts degree RS).1,?_⟩
  intro i j ell hell hell1 z hz hzsupp
  let f : D → ℝ := chi i ∘ (A.chart i).symm
  let pr : X →L[ℝ] D := ContinuousLinearMap.snd ℝ Ep D
  let O : Set X := pr ⁻¹' (A.chart i).target
  have hO : IsOpen O := (A.chart i).open_target.preimage pr.continuous
  have hf : ContDiffOn ℝ ∞ f (A.chart i).target :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))).contDiffOn
  have hfp : ContDiffOn ℝ ∞ (f ∘ pr) O := hf.comp_continuousLinearMap pr
  have hzO : z ∈ O := hz.1
  have hjet (k : ℕ) (hk : k ≤ j) : ell^k*‖iteratedFDeriv ℝ k (f ∘ pr) z‖ ≤ Prefix j := by
    have hb := hbound i i k z.2 hz hzsupp
    have hp := tensor_comp_nonexpansive_linear_jet_le pr (ContinuousLinearMap.norm_snd_le ..)
      (A.chart i).open_target hf hz.1 k
    have hBK : B k ≤ Prefix j := Finset.single_le_sum
      (fun r hr => hB r) (Finset.mem_range.mpr (by omega))
    calc
      _ ≤ ell^k*B k := mul_le_mul_of_nonneg_left (hp.trans hb) (pow_nonneg hell k)
      _ ≤ B k := mul_le_of_le_one_left (hB k) (pow_le_one₀ hell hell1)
      _ ≤ Prefix j := hBK
  have hh := slow_bilinear_jet_bound_norm (ContinuousLinearMap.mul ℝ ℝ) O hO
    (f ∘ pr) (f ∘ pr) hfp hfp j ell (Prefix j) (Prefix j) hell z hzO hjet hjet
  have heq : (fun y : X => (ContinuousLinearMap.mul ℝ ℝ) ((f ∘ pr) y) ((f ∘ pr) y)) =
      (fun y : X => f y.2 * f y.2) := by
    funext y
    rfl
  rw [heq] at hh
  change ell^j*‖iteratedFDeriv ℝ j (fun y : X => f y.2 ^ 2) z‖ ≤ Bt j
  simpa only [Bt, pow_two] using hh

#print axioms actual_uniform_prepared_parent_coordinate_profiles
end GlobalEmbedding.Continuation
