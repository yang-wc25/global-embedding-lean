import Smoothing.ParameterRound2MeanPrimitives
import Smoothing.ParameterRound2TensorSeminorm
import Mathlib.Analysis.Complex.OperatorNorm

/-! The same original global mean in the unchanged original tensor norm.
The native mean is identified from primitive decomposition/nonresonance data.
Only fixed coordinate/model costs occur; there is no atlas-cardinality loss.
All parameter-coordinate inverse maps are retained literally in the functions
whose full joint derivatives are bounded. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N c : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_originalMeanCoordinates_eq
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (q : ℕ) (hq : 1 ≤ q) (tau : ℝ) (htau : 0 < tau)
    (i : Fin A.count × Fin c) (y : Fin (m+1+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i)
    (hW : incrementsOriginalJointPoint A B i y ∈ W) :
    incrementsOriginalTensorCoordinates A B
      (incrementsGlobalPrimaryMeanError F hF g input (q+2) tau) i y =
    fun k => (parameterRound2_globalObservedMeanCoefficient F hF g input (q+2) tau (A.chart i.1)
      ((B i.2).symm (incrementsOriginalParameterPoint y), incrementsOriginalSourcePoint y)
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).re := by
  funext k
  exact parameterRound2_meanPrimitives_coordinate F hF g input W primary h q hq tau htau
    (A.chart i.1) (contMDiffOn_of_mem_maximalAtlas (hA.chart_mem i.1))
    (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i.1))
    ((B i.2).symm (incrementsOriginalParameterPoint y),incrementsOriginalSourcePoint y)
    hy.1 hW (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- Actual coordinate smoothness for the original native tensor submodule. -/
theorem parameterRound2_original_tensor_smooth_of_complex_basis
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (Tfield : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (coeff : (Fin A.count × Fin c) → X → Fin ((m+1)*(m+1)) → ℂ)
    (hcoeff : ∀ i k, ContDiffOn ℝ ∞ (fun z => coeff i z k) ((B i.2).target ×ˢ (A.chart i.1).target))
    (heq : ∀ i y, y ∈ incrementsOriginalDifferentiation A B i →
      incrementsOriginalTensorCoordinates A B Tfield i y =
        fun k => (coeff i ((parameterTensorModelEquiv (m+1) d).symm y) k).re) :
    Tfield ∈ parameterRound2_originalSmoothTensorSpace A B := by
  intro i
  have hreal : ContDiffOn ℝ ∞ (fun z k => (coeff i z k).re)
      ((B i.2).target ×ˢ (A.chart i.1).target) :=
    contDiffOn_pi.2 (fun k => Complex.reCLM.contDiff.comp_contDiffOn (hcoeff i k))
  have hmap : MapsTo (parameterTensorModelEquiv (m+1) d).symm
      (incrementsOriginalDifferentiation A B i) ((B i.2).target ×ˢ (A.chart i.1).target) :=
    fun _ hy => ⟨hy.2,hy.1⟩
  apply (hreal.comp (parameterTensorModelEquiv (m+1) d).symm.contDiff.contDiffOn hmap).congr
  exact fun y hy => heq i y hy

/-- Actual complex basis coefficients give the original real tensor norm.
The equation is on the original differentiation domain; true derivatives are
therefore derivatives of the SAME native tensor, not values of an unrelated array. -/
theorem parameterRound2_original_tensor_norm_of_complex_basis
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (Tfield : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (coeff : (Fin A.count × Fin c) → X → Fin ((m+1)*(m+1)) → ℂ)
    (hcoeff : ∀ i k, ContDiffOn ℝ ∞ (fun z => coeff i z k) ((B i.2).target ×ˢ (A.chart i.1).target))
    (heq : ∀ i y, y ∈ incrementsOriginalDifferentiation A B i →
      incrementsOriginalTensorCoordinates A B Tfield i y =
        fun k => (coeff i ((parameterTensorModelEquiv (m+1) d).symm y) k).re)
    (j : ℕ) (ell K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hK : 0 ≤ K)
    (hjets : ∀ i k, ∀ r ≤ j, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ell^r * ‖iteratedFDeriv ℝ r (fun w => coeff i w k) z‖ ≤ K) :
    paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B Tfield)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B Tfield)
      (incrementsOriginalDifferentiation A B) S).toReal ≤
      (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*K := by
  let a := parameterTensorModelEquiv (m+1) d
  let O := fun i : Fin A.count × Fin c => (B i.2).target ×ˢ (A.chart i.1).target
  let S' := fun i => a ⁻¹' S i
  let realCoeff := fun i z k => (coeff i z k).re
  have hO : ∀ i, IsOpen (O i) := fun i => (B i.2).open_target.prod (A.chart i.1).open_target
  have hSO' : ∀ i, S' i ⊆ O i := by
    intro i z hz
    have hh := hSO i hz
    have he : (incrementsOriginalParameterPoint (a z), incrementsOriginalSourcePoint (a z)) = z :=
      a.symm_apply_apply z
    rw [← he]
    exact ⟨hh.2,hh.1⟩
  have hreal (i) : ContDiffOn ℝ ∞ (realCoeff i) (O i) :=
    contDiffOn_pi.2 (fun k => Complex.reCLM.contDiff.comp_contDiffOn (hcoeff i k))
  have hrealb : ∀ i r, r ≤ j → ∀ z ∈ S' i,
      ell^r*‖iteratedFDeriv ℝ r (realCoeff i) z‖ ≤ K := by
    intro i r hr z hz
    apply parameterRound2_joint_pi_weighted_jet (realCoeff i) z
      ((hreal i).contDiffAt ((hO i).mem_nhds (hSO' i hz))) r ell K hell hK
    intro k
    have h := slow_linear_jet_bound Complex.reCLM (O i) (hO i) (fun w => coeff i w k)
      (hcoeff i k) r ell K hell.le z (hSO' i hz) (hjets i k r hr z hz)
    simpa only [realCoeff,Function.comp_def,Complex.reCLM_apply,Complex.reCLM_norm,one_mul] using h
  have hout := parameterRound2_paperAtlasWeighted_le_of_native_weighted_jets
    a j ell K hell hell1 hK realCoeff O S' hO hSO' hreal hrealb
  have hOeq : modelCoordinateDomains a O = incrementsOriginalDifferentiation A B := by
    funext i
    ext y
    change (incrementsOriginalParameterPoint y ∈ (B i.2).target ∧
      incrementsOriginalSourcePoint y ∈ (A.chart i.1).target) ↔ _
    exact and_comm
  have hSeq : modelCoordinateDomains a S' = S := by
    funext i
    ext y
    simp only [modelCoordinateDomains,S',Set.mem_preimage,a.apply_symm_apply]
  rw [hOeq,hSeq] at hout
  have heqn := paperAtlasWeighted_congr_on 0 j ell
    (incrementsOriginalDifferentiation A B) S hSO heq
  rw [heqn]
  exact hout

/-- Native mean error, with raw qualitative binding and true full-joint
complex coefficient profiles. The latter are produced from raw primitives by
parameterRound2_actual_primitive_globalMean_bounds_uniform_split_scale. -/
theorem parameterRound2_original_globalMean_weighted_norm
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (q : ℕ) (hq : 1 ≤ q) (tau : ℝ) (htau : 0 < tau)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hW : ∀ i, MapsTo (incrementsOriginalJointPoint A B i) (incrementsOriginalDifferentiation A B i) W)
    (j : ℕ) (ell K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hK : 0 ≤ K) :
    let coeff := fun (i : Fin A.count × Fin c) (z : X) (k : Fin ((m+1)*(m+1))) =>
      parameterRound2_globalObservedMeanCoefficient F hF g input (q+2) tau (A.chart i.1)
        ((B i.2).symm z.1,z.2) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    (∀ i k, ContDiffOn ℝ ∞ (fun z => coeff i z k) ((B i.2).target ×ˢ (A.chart i.1).target)) →
    (∀ i k, ∀ r ≤ j, ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ S i →
      ell^r*‖iteratedFDeriv ℝ r (fun w => coeff i w k) z‖ ≤ K) →
    paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B
      (incrementsGlobalPrimaryMeanError F hF g input (q+2) tau))
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B
      (incrementsGlobalPrimaryMeanError F hF g input (q+2) tau))
      (incrementsOriginalDifferentiation A B) S).toReal ≤
      (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*K := by
  intro coeff hcoeff hjets
  exact parameterRound2_original_tensor_norm_of_complex_basis A B
    (incrementsGlobalPrimaryMeanError F hF g input (q+2) tau) S hSO coeff hcoeff
    (fun i y hy => parameterRound2_originalMeanCoordinates_eq A B hA F hF g input
      W primary h q hq tau htau i y hy (hW i hy)) j ell K hell hell1 hK hjets

#print axioms parameterRound2_original_tensor_smooth_of_complex_basis
#print axioms parameterRound2_originalMeanCoordinates_eq
#print axioms parameterRound2_original_tensor_norm_of_complex_basis
#print axioms parameterRound2_original_globalMean_weighted_norm
end GlobalEmbedding.Continuation
