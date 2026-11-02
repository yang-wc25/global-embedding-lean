import Smoothing.ParameterRound2MeanGermResidualMembership
import Smoothing.ParameterRound2TensorGermTransfer

/-! Actual local mean estimates on the ORIGINAL symmetric C0 reserve.
The size and Lipschitz constants are derived from concrete primitive profiles.
No estimate for T, the mean, or any finite residual is supplied. Every input
and difference size is the original weighted tensor seminorm. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N c : ℕ} {M Tr : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_actual_germ_physical_mean_restrict
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho ell : ℝ)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (q : ℕ)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W)
    (epsilon delta : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho})
    (G : Set (Ep × M)) (hG : IsOpen G)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hSG : ∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G) :
    let gG := parameterRound2_restrictPrimaryFamily F g G hG
    let E0 := fun t x => delta^2 •
      (incrementsGlobalPrimaryMean F hF g K.val.val (q+2) (epsilon*ell) t x-H.val t x)
    let EG := fun t x => delta^2 •
      (incrementsGlobalPrimaryMean F hF gG K.val.val (q+2) (epsilon*ell) t x-H.val t x)
    (∀ z ∈ G, EG z.1 z.2 = E0 z.1 z.2) ∧
    EG ∈ parameterRound2_originalTensorGermSpace A B S W ∧
    ∀ base j scale, paperAtlasWeighted base j scale (incrementsOriginalTensorCoordinates A B EG)
      (incrementsOriginalDifferentiation A B) S =
      paperAtlasWeighted base j scale (incrementsOriginalTensorCoordinates A B E0)
        (incrementsOriginalDifferentiation A B) S := by
  intro gG E0 EG
  have hE0 := parameterRound2_actual_germ_physical_mean_mem A B S W p H rho ell F hF g q hsm
    epsilon delta he he1 K
  have heq : ∀ z ∈ G, EG z.1 z.2 = E0 z.1 z.2 := by
    intro z hz
    exact congrArg (fun L => delta^2 • (L-H.val z.1 z.2))
      (parameterRound2_restrictPrimary_mean F hF g G hG K.val.val (q+2) (epsilon*ell) z hz)
  refine ⟨heq,⟨?_,?_⟩,?_⟩
  · exact parameterRound2_tensor_coordinate_germ_transfer A B S hSO E0 EG hE0.1 G hG hSG
      (fun z hz => (heq z hz).symm)
  · intro z hz
    exact ((parameterRound2_actual_native_mean_symmetric F hF gG K.val.val (q+2) (epsilon*ell) z.1 z.2).sub
      (H.property.2 z hz)).smul (delta^2)
  · intro base j scale
    exact parameterRound2_originalTensor_weighted_eq_of_sample_germ A B S hSO EG E0 G hG hSG heq base j scale

#print axioms parameterRound2_actual_germ_physical_mean_restrict
end GlobalEmbedding.Continuation
