import Smoothing.ParameterRound2TensorSeminorm

/-!
# The accepted finite reserve on the SAME original native tensors

The abstract reserve theorem is used without changing or reproving its
threshold argument. Its space is now the genuine tangent-tensor submodule;
every seminorm is definitionally the original full-joint paper norm. The
positive reserve is the literal original C0 norm. The threshold is chosen
before the operator and before any later observation order.

This interface does not assert that an arbitrary supplied operator is the
actual mean. That identification and its local size estimates are the
remaining analytic consumer obligations.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)

theorem parameterRound2_originalTensorSeminorm_zero
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target)
    (ell : ℝ) (T : parameterRound2_originalSmoothTensorSpace A B) :
    parameterRound2_originalTensorSeminorm A B Omega Q hOmega hQ hOmegaTarget hQTarget ell 0 T =
      (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B T.val)
        (incrementsOriginalDifferentiation A B)
        (incrementsOriginalEvaluation A B Omega Q univ)).toReal := by
  rw [parameterRound2_originalTensorSeminorm_apply]
  simp [paperAtlasWeighted]

/-- Native tensor finite backward reserve with the actual original C0
domain and actual original weighted high-order bounds. `q` and `loss` are
fixed before the positive entrance threshold; no observation order enters it. -/
theorem parameterRound2_original_tensor_finite_reserve
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target)
    (ell : ℝ) (H : parameterRound2_originalSmoothTensorSpace A B)
    (rho : ℝ) (hrho : 0 < rho) (C : ℕ → ℝ → ℝ) (q loss : ℕ) (hq : 1 ≤ q) :
    let p := parameterRound2_originalTensorSeminorm A B Omega Q hOmega hQ hOmegaTarget hQTarget ell
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧
      ∀ T : ℝ → {K : parameterRound2_originalSmoothTensorSpace A B // p 0 (K-H) < rho} →
          parameterRound2_originalSmoothTensorSpace A B,
        (∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → ∀ s R
          (K : {K : parameterRound2_originalSmoothTensorSpace A B // p 0 (K-H) < rho}),
          p (s+loss) K.val ≤ R → p s (T epsilon K) ≤ epsilon*C s R) →
        ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
          let K := fun i : ℕ => (meanReserveStep (p 0) H rho (T epsilon))^[i] H
          (∀ i ≤ q, p 0 (K i-H) ≤ rho/2 ∧
            p ((q-i)*loss) (K i) ≤ meanReserveBound p H C q loss i) ∧
          ∀ i < q, ∃ hi : p 0 (K i-H) < rho,
            K (i+1) = H-T epsilon ⟨K i,hi⟩ := by
  intro p
  have hp : ∀ s t, s ≤ t → ∀ K, p s K ≤ p t K := by
    intro s t hst K
    exact parameterRound2_originalTensorSeminorm_mono A B Omega Q hOmega hQ hOmegaTarget hQTarget ell hst K
  exact mean_iteration_finite_reserve p hp H rho hrho C q loss hq

#print axioms parameterRound2_originalTensorSeminorm_zero
#print axioms parameterRound2_original_tensor_finite_reserve
end
end GlobalEmbedding.Continuation
