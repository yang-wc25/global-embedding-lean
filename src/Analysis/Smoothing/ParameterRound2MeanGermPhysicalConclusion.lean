import Smoothing.ParameterRound2ActualGermMeanIteration
import Smoothing.ParameterRound2MeanGermResidualScaling

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

/-! Exact physical finite-mean conclusion. This is a definition of the
literal same solver iterate and the original weighted tensor quantity. -/

def ParameterRound2ActualGermMeanPhysicalResidual
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho ell : ℝ) (q : ℕ)
    (Cmean : ℕ → ℝ) (epsilon0 : ℝ)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W) : Prop :=
    ∀ epsilon, 0 < epsilon → epsilon < epsilon0 →
    let Top := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧
    ∀ (j : ℕ) (delta : ℝ),
    let meanResidual := fun t x => delta^2 •
      (incrementsGlobalPrimaryMean F hF g (K q).val (q+2) (epsilon*ell) t x-H.val t x)
    let value := paperAtlasWeighted 0 j (epsilon*ell)
      (incrementsOriginalTensorCoordinates A B meanResidual) (incrementsOriginalDifferentiation A B) S
    value ≠ ⊤ ∧
    value.toReal ≤ delta^2*(epsilon^(q+1)*Cmean j) ∧
    value.toReal ≤ delta^2*(epsilon^q*Cmean j)

theorem parameterRound2_actual_germ_mean_physical_uniform
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell)
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ) (hrho : 0 < rho)
    (q : ℕ) (hq : 1 ≤ q) (C Cdiff : ℕ → ℝ → ℝ) :
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    ∃ Cmean : ℕ → ℝ, (∀ j, 0 ≤ Cmean j) ∧
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ ∀
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W),
    let Top := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p s (Top epsilon K) ≤ epsilon*C s R) →
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K L : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p (s+(q+4)) L.val ≤ R →
      p s (Top epsilon K-Top epsilon L) ≤ epsilon*Cdiff s R*p (s+(q+4)) (K.val-L.val)) →
    ParameterRound2ActualGermMeanPhysicalResidual A B S W p H rho ell q Cmean epsilon0 F hF g hsm := by
  intro p
  let R := parameterRound2_finiteMeanProfile p H C (q+4)
  let C0 := fun s => max 0 (C s (p (s+(q+4)) H))
  let Cd := fun i s => max 0 (Cdiff s (max (R i (s+(q+4))) (R (i+1) (s+(q+4)))))
  let Cmean := fun j => parameterRound2_finiteMeanErrorCost C0 Cd (q+4) q j
  have hCost (j) : 0 ≤ Cmean j := parameterRound2_finiteMeanErrorCost_nonneg C0 Cd (q+4)
    (fun _ => le_max_left _ _) (fun _ _ => le_max_left _ _) q j
  have hp : ∀ s t, s ≤ t → ∀ K, p s K ≤ p t K := by
    intro s t hst K
    exact parameterRound2_originalTensorGermSeminorm_mono A B S W hS hSO ell hst K
  let epsilon0 := parameterRound2_finiteMeanThreshold p hp H rho hrho C Cdiff q (q+4) hq
  have he0 := parameterRound2_finiteMeanThreshold_pos p hp H rho hrho C Cdiff q (q+4) hq
  refine ⟨Cmean,hCost,epsilon0,he0.1,he0.2,?_⟩
  intro F hF g hsm Top hsize hdiff epsilon he he0lt _ K
  have he1 : epsilon ≤ 1 := he0lt.le.trans he0.2
  have hiter := parameterRound2_actual_original_germ_mean_finite_residual
    A B S W p hp ell H rho hrho q (q+4) hq C Cdiff F hF g hsm hsize hdiff epsilon he he0lt
  obtain ⟨hres,hprofile,E,hE,hEb⟩ := hiter
  refine ⟨hres,?_⟩
  intro j delta meanResidual value
  have hb : p j E ≤ epsilon^(q+1)*Cmean j := hEb j
  have hfast := parameterRound2_original_germ_mean_residual_fast_scale A B S W hS hSO
    E j (epsilon*ell) ell delta (epsilon^(q+1)*Cmean j)
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le) hb
  have hfn : (fun t x => delta^2 • E.val t x) = meanResidual := by rw [hE]
  rw [hfn] at hfast
  exact ⟨hfast.1,hfast.2,hfast.2.trans
    (parameterRound2_mean_q_succ_power_le delta epsilon _ q he.le he1 (hCost j))⟩

#print axioms parameterRound2_actual_germ_mean_physical_uniform
end GlobalEmbedding.Continuation
