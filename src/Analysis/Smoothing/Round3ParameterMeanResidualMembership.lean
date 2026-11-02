import Smoothing.Round3ParameterMeanPhysicalResidual

/-! The actual scaled mean defect lies in the original global symmetric
tensor space.  This follows algebraically from the same operator reserve;
there is no separate smooth-residual assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M P Λ Β : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M] [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_actual_mean_defect_germ_mem
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (F : P → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (K H : parameterRound2_originalTensorGermSpace A B S W) (length : ℕ) (tau delta : ℝ)
    (hT : round3ParameterPrimaryMeanError F hF g K.val length tau ∈
      parameterRound2_originalTensorGermSpace A B S W) :
    (fun t x => delta^2 • (round3ParameterPrimaryMean F hF g K.val length tau t x-H.val t x)) ∈
      parameterRound2_originalTensorGermSpace A B S W := by
  let T : parameterRound2_originalTensorGermSpace A B S W := ⟨_,hT⟩
  have he : (fun t x => delta^2 • (round3ParameterPrimaryMean F hF g K.val length tau t x-H.val t x)) =
      (delta^2 • (K+T-H)).val := by
    funext t x
    change delta^2 • (round3ParameterPrimaryMean F hF g K.val length tau t x-H.val t x) =
      delta^2 • (K.val t x+(round3ParameterPrimaryMean F hF g K.val length tau t x-K.val t x)-H.val t x)
    congr 1
    abel
  rw [he]
  exact (delta^2 • (K+T-H)).property

theorem round3Parameter_actual_iterated_mean_defect_germ_mem
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho ell : ℝ) (hrho : 0 < rho) (q : ℕ)
    (Cmean : ℕ → ℝ) (epsilon0 : ℝ) (he01 : epsilon0 ≤ 1)
    (F : P → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      round3ParameterPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W)
    (hres : Round3ParameterActualMeanPhysicalResidual A B S W p H rho ell q Cmean epsilon0 F hF g hsm)
    (epsilon delta : ℝ) (he : 0 < epsilon) (he0 : epsilon < epsilon0) :
    let Top := round3ParameterMeanReserveOperator A B S W p H rho ell F hF g q hsm
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (fun t x => delta^2 • (round3ParameterPrimaryMean F hF g (K q).val (q+2) (epsilon*ell) t x-H.val t x)) ∈
      parameterRound2_originalTensorGermSpace A B S W := by
  intro Top K
  have hK : p 0 (K q-H) < rho := ((hres epsilon he he0).1 q le_rfl).trans_lt (by linarith)
  exact round3Parameter_actual_mean_defect_germ_mem A B S W F hF g (K q) H (q+2) (epsilon*ell) delta
    (hsm epsilon he (he0.le.trans he01) ⟨K q,hK⟩)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_iterated_mean_defect_germ_mem
