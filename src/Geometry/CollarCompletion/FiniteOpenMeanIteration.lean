import CollarCompletion.FiniteOpenMeanOperator
import Smoothing.ParameterRound2UniformMeanIteration

/-!
# One actual finite mean trajectory in the unchanged original norms

The numerical threshold and residual profile depend only on the supplied
numerical input profiles and the fixed order q. The same physical mean map
is iterated q times before any observation order is selected. The analytic
premises below are produced by `original_finite_mean_estimates`; they are
not additional hypotheses of the original-input entrance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation.CollarCompletion
open SourceCollarsBridge

/-- Purely numerical residual cost, fixed before any datum or atlas. -/
def finitePhysicalMeanCost (B0 : ℕ → ℝ) (C Cdiff : ℕ → ℝ → ℝ) (q j : ℕ) : ℝ :=
  let R := parameterRound2_uniformMeanProfile B0 C (q+4)
  let C0 := fun s => max 0 (C s (B0 (s+(q+4))))
  let Cd := fun i s => max 0 (Cdiff s (max (R i (s+(q+4))) (R (i+1) (s+(q+4)))))
  parameterRound2_finiteMeanErrorCost C0 Cd (q+4) q j

theorem finitePhysicalMeanCost_nonneg
    (B0 : ℕ → ℝ) (C Cdiff : ℕ → ℝ → ℝ) (q j : ℕ) :
    0 ≤ finitePhysicalMeanCost B0 C Cdiff q j :=
  parameterRound2_finiteMeanErrorCost_nonneg _ _ (q+4)
    (fun _ => le_max_left _ _) (fun _ _ => le_max_left _ _) q j

variable {m d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

/-- The same literal physical mean gives all-order residual estimates on
arbitrary original norm domains. No compactness is used. -/
theorem finite_actual_mean_iterate_tensor
    (B0 : ℕ → ℝ) (C Cdiff : ℕ → ℝ → ℝ) (rho : ℝ) (hrho : 0 < rho) (q : ℕ)
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (H : finiteTensorGermSpace A B S W hSO)
    (F : P → M → V)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source → ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F z.1))
    (hsm : actualFiniteMeanMembership A B S W hSO ell H rho F g hActive q) :
    let p := finiteTensorGermSeminorm A B S W hSO ell
    let Top := actualFiniteMeanOperator A B S W hSO ell H rho F g hActive q hsm
    (∀ s, p s H ≤ B0 s) →
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K : {K : finiteTensorGermSpace A B S W hSO // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p s (Top epsilon K) ≤ epsilon*C s R) →
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K L : {K : finiteTensorGermSpace A B S W hSO // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p (s+(q+4)) L.val ≤ R →
      p s (Top epsilon K-Top epsilon L) ≤ epsilon*Cdiff s R*p (s+(q+4)) (K.val-L.val)) →
    ∀ epsilon, 0 < epsilon →
      epsilon < parameterRound2_uniformMeanThreshold B0 C rho q (q+4) →
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧
    (∀ i ≤ q, ∀ s, p s (K i) ≤ parameterRound2_uniformMeanProfile B0 C (q+4) i s) ∧
    ∃ E : finiteTensorGermSpace A B S W hSO,
      E.val.val = (fun t x =>
        fullIncrementNovPrimaryMean F g (K q).val.val hActive (q+2) (epsilon*ell) t x-H.val.val t x) ∧
      ∀ j, p j E ≤ epsilon^(q+1)*finitePhysicalMeanCost B0 C Cdiff q j := by
  intro p Top hH hsize hdiff epsilon he he0 K
  have he1 : epsilon ≤ 1 := he0.le.trans
    (parameterRound2_uniformMeanThreshold_pos B0 C rho hrho q (q+4)).2
  have hiter := parameterRound2_uniform_mean_finite_residual B0 C Cdiff rho hrho q (q+4)
    p H hH Top hsize hdiff epsilon he he0
  obtain ⟨hres,hprofile,hdom,hfinal⟩ := hiter
  let Tout := Top epsilon ⟨K q,hdom⟩
  let Eout : finiteTensorGermSpace A B S W hSO := K q+Tout-H
  have hTv : Tout.val.val = fullIncrementNovPrimaryMeanError F g (K q).val.val hActive
      (q+2) (epsilon*ell) :=
    actualFiniteMeanOperator_value A B S W hSO ell H rho F g hActive q hsm epsilon ⟨K q,hdom⟩ he he1
  have hE : Eout.val.val = fun t x =>
      fullIncrementNovPrimaryMean F g (K q).val.val hActive (q+2) (epsilon*ell) t x-H.val.val t x := by
    funext t x
    change (K q).val.val t x+Tout.val.val t x-H.val.val t x = _
    rw [hTv]
    change (K q).val.val t x+
      (fullIncrementNovPrimaryMean F g (K q).val.val hActive (q+2) (epsilon*ell) t x-(K q).val.val t x)-
      H.val.val t x = _
    abel
  exact ⟨hres,hprofile,Eout,hE,fun j => hfinal j⟩

/-- The same literal physical mean gives all-order residual estimates on
arbitrary original norm domains. No compactness is used. -/
theorem finite_actual_mean_iterate_residual
    (B0 : ℕ → ℝ) (C Cdiff : ℕ → ℝ → ℝ) (rho : ℝ) (hrho : 0 < rho) (q : ℕ)
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (H : finiteTensorGermSpace A B S W hSO)
    (F : P → M → V)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source → ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F z.1))
    (hsm : actualFiniteMeanMembership A B S W hSO ell H rho F g hActive q) :
    let p := finiteTensorGermSeminorm A B S W hSO ell
    let Top := actualFiniteMeanOperator A B S W hSO ell H rho F g hActive q hsm
    (∀ s, p s H ≤ B0 s) →
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K : {K : finiteTensorGermSpace A B S W hSO // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p s (Top epsilon K) ≤ epsilon*C s R) →
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K L : {K : finiteTensorGermSpace A B S W hSO // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p (s+(q+4)) L.val ≤ R →
      p s (Top epsilon K-Top epsilon L) ≤ epsilon*Cdiff s R*p (s+(q+4)) (K.val-L.val)) →
    ∀ epsilon, 0 < epsilon →
      epsilon < parameterRound2_uniformMeanThreshold B0 C rho q (q+4) →
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧
    (∀ i ≤ q, ∀ s, p s (K i) ≤ parameterRound2_uniformMeanProfile B0 C (q+4) i s) ∧
    ∀ (j : ℕ) (delta : ℝ),
    let meanResidual := fun t x => delta^2 •
      (fullIncrementNovPrimaryMean F g (K q).val.val hActive (q+2) (epsilon*ell) t x-H.val.val t x)
    let value := paperAtlasWeighted 0 j (epsilon*ell)
      (incrementsOriginalTensorCoordinates A B meanResidual) (incrementsOriginalDifferentiation A B) S
    meanResidual ∈ parameterRound2_originalTensorGermSpace A B S W ∧
    value ≠ ⊤ ∧ value.toReal ≤ delta^2*(epsilon^(q+1)*finitePhysicalMeanCost B0 C Cdiff q j) := by
  intro p Top hH hsize hdiff epsilon he he0 K
  have he1 : epsilon ≤ 1 := he0.le.trans
    (parameterRound2_uniformMeanThreshold_pos B0 C rho hrho q (q+4)).2
  have hiter := parameterRound2_uniform_mean_finite_residual B0 C Cdiff rho hrho q (q+4)
    p H hH Top hsize hdiff epsilon he he0
  obtain ⟨hres,hprofile,hdom,hfinal⟩ := hiter
  let Tout := Top epsilon ⟨K q,hdom⟩
  let Eout : finiteTensorGermSpace A B S W hSO := K q+Tout-H
  have hTv : Tout.val.val = fullIncrementNovPrimaryMeanError F g (K q).val.val hActive
      (q+2) (epsilon*ell) :=
    actualFiniteMeanOperator_value A B S W hSO ell H rho F g hActive q hsm epsilon ⟨K q,hdom⟩ he he1
  have hE : Eout.val.val = fun t x =>
      fullIncrementNovPrimaryMean F g (K q).val.val hActive (q+2) (epsilon*ell) t x-H.val.val t x := by
    funext t x
    change (K q).val.val t x+Tout.val.val t x-H.val.val t x = _
    rw [hTv]
    change (K q).val.val t x+
      (fullIncrementNovPrimaryMean F g (K q).val.val hActive (q+2) (epsilon*ell) t x-(K q).val.val t x)-
      H.val.val t x = _
    abel
  refine ⟨hres,hprofile,?_⟩
  intro j delta meanResidual value
  have hb : p j Eout ≤ epsilon^(q+1)*finitePhysicalMeanCost B0 C Cdiff q j := hfinal j
  have hfast := finite_original_mean_residual_fast_scale A B S W hSO ell Eout j
    (epsilon*ell) delta (epsilon^(q+1)*finitePhysicalMeanCost B0 C Cdiff q j)
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le) hb
  have hfn : (fun t x => delta^2 • Eout.val.val t x) = meanResidual := by rw [hE]
  have hmem : (fun t x => delta^2 • Eout.val.val t x) ∈
      parameterRound2_originalTensorGermSpace A B S W :=
    (delta^2 • Eout).val.property
  rw [hfn] at hfast hmem
  exact ⟨hmem,hfast⟩

end GlobalEmbedding.Continuation.CollarCompletion
#print axioms GlobalEmbedding.Continuation.CollarCompletion.finitePhysicalMeanCost_nonneg
#print axioms GlobalEmbedding.Continuation.CollarCompletion.finite_actual_mean_iterate_tensor
#print axioms GlobalEmbedding.Continuation.CollarCompletion.finite_actual_mean_iterate_residual
