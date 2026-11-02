import Smoothing.Round3ParameterMeanNorms
import Mathlib.Analysis.Complex.OperatorNorm

/-! Real native tensor coefficients retain the same original source-first
atlas norm, on the original differentiation domain and true sample germs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

theorem actual_original_tensor_norm_of_real_germs
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Tfield : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (O : Fin A.count × Fin c → Set X) (hO : ∀ i, IsOpen (O i))
    (hOsub : ∀ i, O i ⊆ (B i.2).target ×ˢ (A.chart i.1).target)
    (hSO : ∀ i, (parameterTensorModelEquiv (m+1) d) ⁻¹' S i ⊆ O i)
    (coeff : (Fin A.count × Fin c) → X → Fin ((m+1)*(m+1)) → ℝ)
    (hcoeff : ∀ i k, ContDiffOn ℝ ∞ (fun z => coeff i z k) (O i))
    (heq : ∀ i y, (parameterTensorModelEquiv (m+1) d).symm y ∈ O i →
      incrementsOriginalTensorCoordinates A B Tfield i y =
        coeff i ((parameterTensorModelEquiv (m+1) d).symm y))
    (j : ℕ) (ell K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hK : 0 ≤ K)
    (hjets : ∀ i k, ∀ s ≤ j, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ell^s*‖iteratedFDeriv ℝ s (fun w => coeff i w k) z‖ ≤ K) :
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B Tfield i)
      ((parameterTensorModelEquiv (m+1) d).symm ⁻¹' O i)) ∧
    paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B Tfield)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B Tfield)
      (incrementsOriginalDifferentiation A B) S).toReal ≤
      (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*K := by
  apply round3Parameter_original_tensor_norm_of_complex_germs A B Tfield S O hO hOsub hSO
    (fun i z k => (coeff i z k : ℂ))
    (fun i k => Complex.ofRealCLM.contDiff.comp_contDiffOn (hcoeff i k))
    (fun i y hy => by simpa only [Complex.ofReal_re] using heq i y hy)
    j ell K hell hell1 hK
  intro i k s hs z hz
  have hh := slow_linear_jet_bound Complex.ofRealCLM (O i) (hO i) (fun w => coeff i w k)
    (hcoeff i k) s ell K hell.le z (hSO i hz) (hjets i k s hs z hz)
  simpa only [Function.comp_def,Complex.ofRealCLM_apply,Complex.ofRealCLM_norm,one_mul] using hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_tensor_norm_of_real_germs
