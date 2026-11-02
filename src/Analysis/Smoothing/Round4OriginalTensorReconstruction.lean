import Smoothing.Round4OriginalNativeTensor
import Smoothing.Round4ActualHostGoodPhases

/-! Literal intrinsic tensor reconstruction from the same native rank-one
identity. Every covector is the real differential of the same host phase.
Both inverse/forward chart derivatives cancel exactly; no norm comparison
or replacement tensor appears. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators NNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance templateNormalRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance templateNormalSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {d m N cParam : ℕ} {P : Type*} [TopologicalSpace P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance templateNormalFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance templateNormalFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance templateNormalHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance templateNormalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance templateNormalTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance templateNormalTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance templateNormalTangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance templateNormalTangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance templateNormalTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance

def round4HostPhaseCovector (host : OpenPartialHomeomorph M D)
    (xi : D →L[ℝ] ℝ) (x : M) : TangentSpace 𝓙 x →L[ℝ] ℝ :=
  (tangentSpaceCastModel 𝓘(ℝ,ℝ) (xi (host x))).toContinuousLinearMap.comp
    (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun y => xi (host y)) x)

theorem round4HostPhaseCovector_eq
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (xi : D →L[ℝ] ℝ) (x : D) (hx : x ∈ host.target) :
    round4HostPhaseCovector host xi (host.symm x) =
      xi.comp (mfderiv 𝓙 𝓙 host (host.symm x)) :=
  round4_actual_host_linear_phase_covector host hhost xi x hx

theorem round4_original_rank_one_reconstruction
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Aatlas : BufferedAtlas M D) (Bparam : Fin cParam → OpenPartialHomeomorph P Ep)
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (i : Fin Aatlas.count × Fin cParam)
    (hhost : Aatlas.chart i.1 ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (z : X) (hz : parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalDifferentiation Aatlas Bparam i)
    (xi : ι → κ → D →L[ℝ] ℝ) (amplitude : ι → κ → ℝ)
    (hRec : (∑ q : ι, continuousRankOneReconstruct (xi q) (fun a => amplitude q a ^ 2)) =
      round4OriginalNativeTensorCoordinates Aatlas Bparam Htensor i z) :
    let x := incrementsOriginalJointPoint Aatlas Bparam i (parameterTensorModelEquiv (m+1) d z)
    ∀ u v : TangentSpace 𝓙 x.2, Htensor x.1 x.2 u v =
      ∑ q : ι, ∑ a : κ, amplitude q a ^ 2 *
        round4HostPhaseCovector (Aatlas.chart i.1) (xi q a) x.2 u *
        round4HostPhaseCovector (Aatlas.chart i.1) (xi q a) x.2 v := by
  classical
  intro x u v
  let y := parameterTensorModelEquiv (m+1) d z
  let host := Aatlas.chart i.1
  have hcoord : incrementsOriginalSourcePoint y ∈ host.target := hz.1
  let J := actualIncrementChartDerivativeEquiv host hhost (incrementsOriginalSourcePoint y) hcoord
  have hPull := round4_original_tensor_coordinates_pullback Aatlas Bparam Htensor i y
  have hNative (a b : D) : round4OriginalNativeTensorCoordinates Aatlas Bparam Htensor i z a b =
      Htensor x.1 x.2 (J a) (J b) := by
    exact congrArg (fun Q : LinearMap.BilinForm ℝ D => Q a b) hPull
  have hPhase (q : ι) (a : κ) : round4HostPhaseCovector host (xi q a) x.2 =
      (xi q a).comp J.symm.toContinuousLinearMap :=
    round4HostPhaseCovector_eq host hhost (xi q a) (incrementsOriginalSourcePoint y) hcoord
  have hEval := congrArg (fun Q : D →L[ℝ] D →L[ℝ] ℝ => Q (J.symm u) (J.symm v)) hRec
  simp only [ContinuousLinearMap.sum_apply,continuousRankOneReconstruct_apply] at hEval
  calc
    Htensor x.1 x.2 u v = round4OriginalNativeTensorCoordinates Aatlas Bparam Htensor i z
        (J.symm u) (J.symm v) := by
      rw [hNative,J.apply_symm_apply,J.apply_symm_apply]
    _ = ∑ q : ι, ∑ a : κ, amplitude q a ^ 2 * xi q a (J.symm u) * xi q a (J.symm v) := hEval.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro a _
      rw [hPhase q a]
      rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_original_rank_one_reconstruction
