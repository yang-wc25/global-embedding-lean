import Smoothing.ParameterRound2ActualGermMeanIteration

/-! Actual local mean estimates on the ORIGINAL symmetric C0 reserve.
The size and Lipschitz constants are derived from concrete primitive profiles.
No estimate for T, the mean, or any finite residual is supplied. Every input
and difference size is the original weighted tensor seminorm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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

private theorem normalize_raw_mean_size (C epsilon ell : ℝ) (hell : ell ≠ 0) :
    C*((epsilon*ell)/ell) = epsilon*C := by
  rw [mul_div_cancel_right₀ epsilon hell]
  exact mul_comm _ _

private theorem normalize_raw_mean_difference (C epsilon ell Dcoef x : ℝ) (hell : ell ≠ 0) :
    C*((epsilon*ell)/ell)*(Dcoef*x) = epsilon*(C*Dcoef)*x := by
  rw [mul_div_cancel_right₀ epsilon hell]
  ring

theorem parameterRound2_actual_germ_mean_operator_size
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell)
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (q : ℕ) :
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    ∀ (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W),
    let Top := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
    ∀ (K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}) (s : ℕ) (C : ℝ),
      (paperAtlasWeighted 0 s ell (incrementsOriginalTensorCoordinates A B
        (incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell)))
        (incrementsOriginalDifferentiation A B) S).toReal ≤ C*((epsilon*ell)/ell) →
      p s (Top epsilon K) ≤ epsilon*C := by
  intro p hsm Top epsilon he he1 K s C hb
  change parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell s
    (Top epsilon K) ≤ _
  rw [parameterRound2_originalTensorGermSeminorm_apply,
    parameterRound2_actualGermMeanReserveOperator_val A B S W p H rho ell F hF g q hsm epsilon K he he1]
  exact hb.trans_eq (normalize_raw_mean_size C epsilon ell hell.ne')

theorem parameterRound2_actual_germ_mean_operator_difference
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell)
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (q : ℕ) :
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    ∀ (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W),
    let Top := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
    ∀ (K L : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho})
      (s loss : ℕ) (C Dcoef : ℝ),
      (paperAtlasWeighted 0 s ell (incrementsOriginalTensorCoordinates A B
        (fun t x => incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) t x-
          incrementsGlobalPrimaryMeanError F hF g L.val.val (q+2) (epsilon*ell) t x))
        (incrementsOriginalDifferentiation A B) S).toReal ≤
          C*((epsilon*ell)/ell)*(Dcoef*p (s+loss) (K.val-L.val)) →
      p s (Top epsilon K-Top epsilon L) ≤ epsilon*(C*Dcoef)*p (s+loss) (K.val-L.val) := by
  intro p hsm Top epsilon he he1 K L s loss C Dcoef hb
  change parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell s
    (Top epsilon K-Top epsilon L) ≤ _
  rw [parameterRound2_originalTensorGermSeminorm_apply]
  change (paperAtlasWeighted 0 s ell (incrementsOriginalTensorCoordinates A B
    (fun t x => (Top epsilon K).val t x-(Top epsilon L).val t x))
    (incrementsOriginalDifferentiation A B) S).toReal ≤ _
  rw [parameterRound2_actualGermMeanReserveOperator_val A B S W p H rho ell F hF g q hsm epsilon K he he1,
    parameterRound2_actualGermMeanReserveOperator_val A B S W p H rho ell F hF g q hsm epsilon L he he1]
  exact hb.trans_eq (normalize_raw_mean_difference C epsilon ell Dcoef
    (p (s+loss) (K.val-L.val)) hell.ne')

#print axioms parameterRound2_actual_germ_mean_operator_difference
end GlobalEmbedding.Continuation
