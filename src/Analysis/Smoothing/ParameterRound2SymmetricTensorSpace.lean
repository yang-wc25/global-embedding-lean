import Smoothing.ParameterRound2TensorSeminorm
import Smoothing.ParameterRound2GlobalMeanIdentity

/-! The actual finite mean iteration takes place in genuine smooth symmetric
native tensor fields. The original decomposition neighborhood is a neighborhood
in this space; no assertion about skew inputs is introduced. Its seminorm is
exactly the unchanged original weighted norm, restricted by a proved linear map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)

def parameterRound2_originalSymmetricTensorSpace
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) :
    Submodule ℝ ((p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x)) where
  carrier := {T | T ∈ parameterRound2_originalSmoothTensorSpace A B ∧ ∀ p x, (T p x).IsSymm}
  zero_mem' := ⟨(parameterRound2_originalSmoothTensorSpace A B).zero_mem,
    fun _ _ => LinearMap.BilinForm.isSymm_zero⟩
  add_mem' := fun hT hU => ⟨(parameterRound2_originalSmoothTensorSpace A B).add_mem hT.1 hU.1,
    fun p x => (hT.2 p x).add (hU.2 p x)⟩
  smul_mem' := fun a T hT => ⟨(parameterRound2_originalSmoothTensorSpace A B).smul_mem a hT.1,
    fun p x => (hT.2 p x).smul a⟩

instance parameterRound2_originalSymmetricTensorSpace_addCommGroup
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) :
    AddCommGroup (parameterRound2_originalSymmetricTensorSpace A B) :=
  @Submodule.addCommGroup ℝ
    ((p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    inferInstance inferInstance inferInstance (parameterRound2_originalSymmetricTensorSpace A B)

instance parameterRound2_originalSymmetricTensorSpace_module
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) :
    Module ℝ (parameterRound2_originalSymmetricTensorSpace A B) :=
  @Submodule.module ℝ
    ((p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    inferInstance inferInstance inferInstance (parameterRound2_originalSymmetricTensorSpace A B)

def parameterRound2_symmetricToSmooth
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) :
    parameterRound2_originalSymmetricTensorSpace A B →ₗ[ℝ] parameterRound2_originalSmoothTensorSpace A B where
  toFun := fun T => ⟨T.val,T.property.1⟩
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def parameterRound2_originalSymmetricSeminorm
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target) (ell : ℝ) (j : ℕ) :
    Seminorm ℝ (parameterRound2_originalSymmetricTensorSpace A B) :=
  (parameterRound2_originalTensorSeminorm A B Omega Q hOmega hQ hOmegaTarget hQTarget ell j).comp
    (parameterRound2_symmetricToSmooth A B)

theorem parameterRound2_originalSymmetricSeminorm_apply
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target) (ell : ℝ) (j : ℕ)
    (T : parameterRound2_originalSymmetricTensorSpace A B) :
    parameterRound2_originalSymmetricSeminorm A B Omega Q hOmega hQ hOmegaTarget hQTarget ell j T =
    (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q univ)).toReal := rfl

theorem parameterRound2_originalSymmetricSeminorm_mono
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target) (ell : ℝ) {j k : ℕ} (hjk : j ≤ k)
    (T : parameterRound2_originalSymmetricTensorSpace A B) :
    parameterRound2_originalSymmetricSeminorm A B Omega Q hOmega hQ hOmegaTarget hQTarget ell j T ≤
    parameterRound2_originalSymmetricSeminorm A B Omega Q hOmega hQ hOmegaTarget hQTarget ell k T :=
  parameterRound2_originalTensorSeminorm_mono A B Omega Q hOmega hQ hOmegaTarget hQTarget ell hjk
    (parameterRound2_symmetricToSmooth A B T)

section Mean
variable {E H0 M0 Ep0 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H0] {I : ModelWithCorners ℝ E H0}
  [TopologicalSpace M0] [ChartedSpace H0 M0] [IsManifold I ∞ M0]
  [BoundarylessManifold I M0] [NormedAddCommGroup Ep0] [NormedSpace ℝ Ep0]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]

theorem parameterRound2_actual_native_mean_symmetric
    (F : Ep0 → M0 → EuclideanSpace ℝ (Fin N))
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep0) → (x : M0) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (p : Ep0) (x : M0) :
    (incrementsGlobalPrimaryMean F hF g input length tau p x).IsSymm := by
  constructor
  intro v w
  simp only [incrementsGlobalPrimaryMean,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.add_apply,LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,
    innerₗ_apply_apply,smul_eq_mul]
  simp_rw [real_inner_comm]

theorem parameterRound2_actual_native_meanError_symmetric
    (F : Ep0 → M0 → EuclideanSpace ℝ (Fin N))
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep0) → (x : M0) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (hInput : ∀ p x, (input p x).IsSymm) (length : ℕ) (tau : ℝ) (p : Ep0) (x : M0) :
    (incrementsGlobalPrimaryMeanError F hF g input length tau p x).IsSymm :=
  (parameterRound2_actual_native_mean_symmetric F hF g input length tau p x).sub (hInput p x)
end Mean

#print axioms parameterRound2_originalSymmetricSeminorm_apply
#print axioms parameterRound2_actual_native_meanError_symmetric
end GlobalEmbedding.Continuation
