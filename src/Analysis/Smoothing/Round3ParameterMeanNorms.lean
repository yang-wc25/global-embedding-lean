import Smoothing.ParameterRound2MeanNativeNorms
import Smoothing.ParameterRound2NativeTensorGermNorms

/-! Arbitrary-parameter actual tensor norm extraction on a genuine local joint neighborhood.
The unchanged original differentiation domain is recovered by the proved
open-restriction identity. There is no global smoothness requirement beyond
the true samples, and every parameter-coordinate direction is retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem round3Parameter_original_tensor_norm_of_complex_germs
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Tfield : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (O : Fin A.count × Fin c → Set X)
    (hO : ∀ i, IsOpen (O i))
    (hOsub : ∀ i, O i ⊆ (B i.2).target ×ˢ (A.chart i.1).target)
    (hSO : ∀ i, (parameterTensorModelEquiv (m+1) d) ⁻¹' S i ⊆ O i)
    (coeff : (Fin A.count × Fin c) → X → Fin ((m+1)*(m+1)) → ℂ)
    (hcoeff : ∀ i k, ContDiffOn ℝ ∞ (fun z => coeff i z k) (O i))
    (heq : ∀ i y, (parameterTensorModelEquiv (m+1) d).symm y ∈ O i →
      incrementsOriginalTensorCoordinates A B Tfield i y =
        fun k => (coeff i ((parameterTensorModelEquiv (m+1) d).symm y) k).re)
    (j : ℕ) (ell K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hK : 0 ≤ K)
    (hjets : ∀ i k, ∀ r ≤ j, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ell^r * ‖iteratedFDeriv ℝ r (fun w => coeff i w k) z‖ ≤ K) :
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B Tfield i)
      ((parameterTensorModelEquiv (m+1) d).symm ⁻¹' O i)) ∧
    paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B Tfield)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B Tfield)
      (incrementsOriginalDifferentiation A B) S).toReal ≤
      (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*K := by
  let a := parameterTensorModelEquiv (m+1) d
  let S' := fun i => a ⁻¹' S i
  let realCoeff := fun i z k => (coeff i z k).re
  have hreal (i) : ContDiffOn ℝ ∞ (realCoeff i) (O i) :=
    contDiffOn_pi.2 (fun k => Complex.reCLM.contDiff.comp_contDiffOn (hcoeff i k))
  have hrealb : ∀ i r, r ≤ j → ∀ z ∈ S' i,
      ell^r*‖iteratedFDeriv ℝ r (realCoeff i) z‖ ≤ K := by
    intro i r hr z hz
    apply parameterRound2_joint_pi_weighted_jet (realCoeff i) z
      ((hreal i).contDiffAt ((hO i).mem_nhds (hSO i hz))) r ell K hell hK
    intro k
    have h := slow_linear_jet_bound Complex.reCLM (O i) (hO i) (fun w => coeff i w k)
      (hcoeff i k) r ell K hell.le z (hSO i hz) (hjets i k r hr z hz)
    simpa only [realCoeff,Function.comp_def,Complex.reCLM_apply,Complex.reCLM_norm,one_mul] using h
  have hreg (i) : ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B Tfield i)
      (a.symm ⁻¹' O i) := by
    apply ((hreal i).comp a.symm.contDiff.contDiffOn (fun y hy => hy)).congr
    exact fun y hy => heq i y hy
  have hout := parameterRound2_paperAtlasWeighted_le_of_native_weighted_jets
    a j ell K hell hell1 hK realCoeff O S' hO hSO hreal hrealb
  have hSeq : modelCoordinateDomains a S' = S := by
    funext i
    ext y
    simp only [modelCoordinateDomains,S',Set.mem_preimage,a.apply_symm_apply]
  rw [hSeq] at hout
  have hSU : ∀ i, S i ⊆ modelCoordinateDomains a O i := by
    intro i y hy
    change a.symm y ∈ O i
    exact hSO i (by change a (a.symm y) ∈ S i; simpa only [a.apply_symm_apply] using hy)
  have hU : ∀ i, IsOpen (modelCoordinateDomains a O i) :=
    fun i => (hO i).preimage a.symm.continuous
  have hUOrig : ∀ i, modelCoordinateDomains a O i ⊆ incrementsOriginalDifferentiation A B i := by
    intro i y hy
    have h := hOsub i hy
    exact ⟨h.2,h.1⟩
  have heqn := paperAtlasWeighted_congr_on 0 j ell (modelCoordinateDomains a O) S hSU heq
  have hrestrict := actual_paperAtlasWeighted_open_restrict 0 j ell
    (incrementsOriginalTensorCoordinates A B Tfield) (incrementsOriginalDifferentiation A B)
    (modelCoordinateDomains a O) S (parameterRound2_originalDifferentiation_open A B) hU hUOrig hSU
  refine ⟨hreg,?_⟩
  rw [hrestrict,heqn]
  exact hout

#print axioms round3Parameter_original_tensor_norm_of_complex_germs
end GlobalEmbedding.Continuation
