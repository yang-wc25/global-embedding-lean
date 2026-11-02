import Smoothing.Round3ParameterMeanResidualMembership
import Smoothing.Round3ParameterPrimaryRestrictionMean
import Smoothing.ParameterRound2TensorGermTransfer

/-! The one global mean iterate may select a single actual positivity
domain for the final construction. Restricting the primary charts at that
point preserves the same mean and every original weighted norm. Neither
the global operator nor Kq is recomputed in a parameter chart or in G. -/

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

theorem round3Parameter_same_mean_residual_on_final_domain
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho ell : ℝ) (hrho : 0 < rho) (q : ℕ)
    (Cmean : ℕ → ℝ) (Theta : ℝ) (hTheta1 : Theta ≤ 1)
    (F : P → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      round3ParameterPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W)
    (hres : Round3ParameterActualMeanPhysicalResidual A B S W p H rho ell q Cmean Theta F hF g hsm)
    (epsilon delta : ℝ) (he : 0 < epsilon) (he0 : epsilon < Theta)
    (G : Set (P × M)) (hG : IsOpen G) (hGW : G ⊆ W)
    (hSG : ∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G) :
    let Top := round3ParameterMeanReserveOperator A B S W p H rho ell F hF g q hsm
    let Kq := (meanReserveStep (p 0) H rho (Top epsilon))^[q] H
    let gG := round3Parameter_restrictPrimaryFamily F g G hG
    let meanResidual := fun t x => delta^2 •
      (round3ParameterPrimaryMean F hF gG Kq.val (q+2) (epsilon*ell) t x-H.val t x)
    meanResidual ∈ parameterRound2_originalTensorGermSpace A B S G ∧
    ∀ j,
      let value := paperAtlasWeighted 0 j (epsilon*ell)
        (incrementsOriginalTensorCoordinates A B meanResidual) (incrementsOriginalDifferentiation A B) S
      value ≠ ⊤ ∧ value.toReal ≤ delta^2*(epsilon^(q+1)*Cmean j) := by
  intro Top Kq gG meanResidual
  let originalResidual := fun t x => delta^2 •
    (round3ParameterPrimaryMean F hF g Kq.val (q+2) (epsilon*ell) t x-H.val t x)
  have hOriginal : originalResidual ∈ parameterRound2_originalTensorGermSpace A B S W :=
    round3Parameter_actual_iterated_mean_defect_germ_mem A B S W p H rho ell hrho q Cmean Theta hTheta1
      F hF g hsm hres epsilon delta he he0
  have heq : ∀ z ∈ G, meanResidual z.1 z.2 = originalResidual z.1 z.2 := by
    intro z hz
    exact congrArg (fun T => delta^2 • (T-H.val z.1 z.2))
      (round3Parameter_restrictPrimary_mean F hF g G hG Kq.val (q+2) (epsilon*ell) z hz)
  refine ⟨?_,?_⟩
  · constructor
    · exact parameterRound2_tensor_coordinate_germ_transfer A B S hSO _ _ hOriginal.1 G hG hSG
        (fun z hz => (heq z hz).symm)
    · intro z hz
      rw [heq z hz]
      exact hOriginal.2 z (hGW hz)
  · intro j value
    have hn := parameterRound2_originalTensor_weighted_eq_of_sample_germ A B S hSO
      meanResidual originalResidual G hG hSG heq 0 j (epsilon*ell)
    have hh := (hres epsilon he he0).2 j delta
    exact (congrArg (fun w : ℝ≥0∞ => w ≠ ⊤ ∧ w.toReal ≤ delta^2*(epsilon^(q+1)*Cmean j)) hn).mpr
      ⟨hh.1,hh.2.1⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_same_mean_residual_on_final_domain
