import Smoothing.Round3ParameterMeanPhysicalResidual
import Smoothing.ParameterRound2UniformMeanIteration

/-! The literal global mean on arbitrary parameters has one numerical
threshold and one numerical residual profile BEFORE the parameter atlas,
original tensor H, fields, scale and primitive family. The iteration is in
the same original tensor space, and retains the q+1 actual residual. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uTr uP uΛ uΒ
variable {m d N c : ℕ} {M : Type uM} {Tr : Type uTr} {P : Type uP} {Λ : Type uΛ} {Β : Type uΒ}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_actual_global_mean_uniform_threshold
    (B0 : ℕ → ℝ) (C Cdiff : ℕ → ℝ → ℝ)
    (rho : ℝ) (hrho : 0 < rho) (q : ℕ) :
    let epsilon0 := parameterRound2_uniformMeanThreshold B0 C rho q (q+4)
    0 < epsilon0 ∧ epsilon0 ≤ 1 ∧
    ∃ Cmean : ℕ → ℝ, (∀ j, 0 ≤ Cmean j) ∧ ∀ (P : Type uP) [TopologicalSpace P] {Λ : Type uΛ} {Β : Type uΒ} [Fintype Λ] [Fintype Β] {c : ℕ}
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell)
    (H : parameterRound2_originalTensorGermSpace A B S W),
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    (∀ s, p s H ≤ B0 s) → ∀
    (F : P → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      round3ParameterPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W),
    let Top := round3ParameterMeanReserveOperator A B S W p H rho ell F hF g q hsm
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p s (Top epsilon K) ≤ epsilon*C s R) →
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K L : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p (s+(q+4)) L.val ≤ R →
      p s (Top epsilon K-Top epsilon L) ≤ epsilon*Cdiff s R*p (s+(q+4)) (K.val-L.val)) →
    Round3ParameterActualMeanPhysicalResidual A B S W p H rho ell q Cmean epsilon0 F hF g hsm := by
  intro epsilon0
  let R := parameterRound2_uniformMeanProfile B0 C (q+4)
  let C0 := fun s => max 0 (C s (B0 (s+(q+4))))
  let Cd := fun i s => max 0 (Cdiff s (max (R i (s+(q+4))) (R (i+1) (s+(q+4)))))
  let Cmean := fun j => parameterRound2_finiteMeanErrorCost C0 Cd (q+4) q j
  have hCost (j) : 0 ≤ Cmean j := parameterRound2_finiteMeanErrorCost_nonneg C0 Cd (q+4)
    (fun _ => le_max_left _ _) (fun _ _ => le_max_left _ _) q j
  have he0 := parameterRound2_uniformMeanThreshold_pos B0 C rho hrho q (q+4)
  refine ⟨he0.1,he0.2,Cmean,hCost,?_⟩
  intro P _ Λ Β _ _ c A B S W hS hSO ell hell H p hH F hF g hsm Top hsize hdiff epsilon he he0lt _ K
  have he1 : epsilon ≤ 1 := he0lt.le.trans he0.2
  have hiter := parameterRound2_uniform_mean_finite_residual B0 C Cdiff rho hrho q (q+4)
    p H hH Top hsize hdiff epsilon he he0lt
  obtain ⟨hres,hprofile,hdom,hfinal⟩ := hiter
  let Tout := Top epsilon ⟨K q,hdom⟩
  let Eout : parameterRound2_originalTensorGermSpace A B S W := K q+Tout-H
  have hTv : Tout.val = round3ParameterPrimaryMeanError F hF g (K q).val (q+2) (epsilon*ell) :=
    round3ParameterMeanReserveOperator_val A B S W p H rho ell F hF g q hsm epsilon ⟨K q,hdom⟩ he he1
  have hE : Eout.val = fun t x => round3ParameterPrimaryMean F hF g (K q).val (q+2)
      (epsilon*ell) t x-H.val t x := by
    funext t x
    change (K q).val t x+Tout.val t x-H.val t x = _
    rw [hTv]
    change (K q).val t x+(round3ParameterPrimaryMean F hF g (K q).val (q+2) (epsilon*ell) t x-
      (K q).val t x)-H.val t x = _
    abel
  refine ⟨hres,?_⟩
  intro j delta meanResidual value
  have hb : p j Eout ≤ epsilon^(q+1)*Cmean j := hfinal j
  have hfast := parameterRound2_original_germ_mean_residual_fast_scale A B S W hS hSO
    Eout j (epsilon*ell) ell delta (epsilon^(q+1)*Cmean j)
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le) hb
  have hfn : (fun t x => delta^2 • Eout.val t x) = meanResidual := by rw [hE]
  rw [hfn] at hfast
  exact ⟨hfast.1,hfast.2,hfast.2.trans
    (parameterRound2_mean_q_succ_power_le delta epsilon _ q he.le he1 (hCost j))⟩


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_global_mean_uniform_threshold
