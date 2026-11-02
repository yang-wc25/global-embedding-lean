import CollarCompletion.FiniteOpenMeanIteration

/-!
# The actual finite-carrier trajectory is the literal native recurrence

The reserve operator is totalized for arbitrary inputs. On the valid
trajectory, the proved reserve bound keeps every used step in its original
branch. This file identifies that same trajectory with the finite native
formula A_0 = H and A_(i+1) = H - T(A_i), without changing any tensor value,
norm domain, or parameter domain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
open SourceCollarsBridge CollarCompletion

variable {m d N c : ℕ} {M P Λ Β : Type*}
  [TopologicalSpace M] [TopologicalSpace P] [Fintype Λ] [Fintype Β]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

/-- The finite native substitutions use precisely the given H and physical
primary mean error. There is no reserve test in this formula. -/
def incrementsCompletionLiteralMeanTrajectory
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (F : P → M → V)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source → ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F z.1))
    (q : ℕ) (tau : ℝ) (i : ℕ) :
    (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) :=
  (fun input => fun p x => H p x-fullIncrementNovPrimaryMeanError F g input hActive (q+2) tau p x)^[i] H

theorem incrementsCompletion_literal_mean_zero
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (F : P → M → V)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source → ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F z.1))
    (q : ℕ) (tau : ℝ) :
    incrementsCompletionLiteralMeanTrajectory H F g hActive q tau 0 = H := rfl

theorem incrementsCompletion_literal_mean_succ
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (F : P → M → V)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source → ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F z.1))
    (q : ℕ) (tau : ℝ) (i : ℕ) :
    incrementsCompletionLiteralMeanTrajectory H F g hActive q tau (i+1) =
      fun p x => H p x-fullIncrementNovPrimaryMeanError F g
        (incrementsCompletionLiteralMeanTrajectory H F g hActive q tau i) hActive (q+2) tau p x := by
  exact Function.iterate_succ_apply' _ i H

theorem incrementsCompletion_actual_mean_step_literal
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (H : finiteTensorGermSpace A B S W hSO) (rho : ℝ) (hrho : 0 < rho)
    (F : P → M → V)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source → ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F z.1))
    (q : ℕ) (hsm : actualFiniteMeanMembership A B S W hSO ell H rho F g hActive q)
    (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    let p := finiteTensorGermSeminorm A B S W hSO ell
    let Top := actualFiniteMeanOperator A B S W hSO ell H rho F g hActive q hsm
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) →
    ∀ i ≤ q, (K (i+1)).val.val = fun t x => H.val.val t x-
      fullIncrementNovPrimaryMeanError F g (K i).val.val hActive (q+2) (epsilon*ell) t x := by
  intro p Top K hReserve i hi
  have hdom : p 0 (K i-H) < rho := (hReserve i hi).trans_lt (by linarith)
  have hStep : K (i+1) = H-Top epsilon ⟨K i,hdom⟩ := by
    change (meanReserveStep (p 0) H rho (Top epsilon))^[i+1] H = _
    rw [Function.iterate_succ_apply']
    change meanReserveStep (p 0) H rho (Top epsilon) (K i) = _
    simp only [meanReserveStep,dite_eq_left hdom]
  have hNative := congrArg
    (fun E : finiteTensorGermSpace A B S W hSO => E.val.val) hStep
  change (K (i+1)).val.val = fun t x => H.val.val t x-
    (Top epsilon ⟨K i,hdom⟩).val.val t x at hNative
  have hValue := actualFiniteMeanOperator_value A B S W hSO ell H rho F g hActive q hsm
    epsilon ⟨K i,hdom⟩ he he1
  rw [hValue] at hNative
  exact hNative

theorem incrementsCompletion_actual_trajectory_eq_literal
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (H : finiteTensorGermSpace A B S W hSO) (rho : ℝ) (hrho : 0 < rho)
    (F : P → M → V)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source → ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F z.1))
    (q : ℕ) (hsm : actualFiniteMeanMembership A B S W hSO ell H rho F g hActive q)
    (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    let p := finiteTensorGermSeminorm A B S W hSO ell
    let Top := actualFiniteMeanOperator A B S W hSO ell H rho F g hActive q hsm
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) →
    ∀ i ≤ q, (K i).val.val = incrementsCompletionLiteralMeanTrajectory H.val.val F g hActive
      q (epsilon*ell) i := by
  intro p Top K hReserve
  have hStep := incrementsCompletion_actual_mean_step_literal A B S W hSO ell H rho hrho
    F g hActive q hsm epsilon he he1 hReserve
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    have hiq : i ≤ q := by omega
    rw [hStep i hiq,incrementsCompletion_literal_mean_succ,ih hiq]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletionLiteralMeanTrajectory
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_literal_mean_zero
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_literal_mean_succ
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_actual_mean_step_literal
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_actual_trajectory_eq_literal
