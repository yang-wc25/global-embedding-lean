import Smoothing.ParameterRound2FiniteMeanIteration
import Smoothing.ParameterRound2TensorGermSpace
import Smoothing.ParameterRound2PrimaryRestrictionMean

/-! Finite mean inversion for the SAME original native symmetric mean tensor.
The iteration is a concrete application of the original global primary solver:
T_epsilon(K) = incrementsGlobalPrimaryMeanError(...,K,q+2,epsilon*ell).
Its input is the genuine smooth symmetric tangent-tensor submodule and every seminorm
is the original source-first full-joint paper norm. The local size/difference
estimates are explicit analytic obligations, supplied by the raw mean chain;
the q+1 residual is derived and is never an input. -/

noncomputable section

open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N c : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Only nonpositive/out-of-range epsilon is totalized; all actual finite
iterates use the literal original mean error on its genuine reserve. -/
def parameterRound2_actualGermMeanReserveOperator
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho ell : ℝ)
    (F : Ep → M → V)
    (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (q : ℕ)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W)
    (epsilon : ℝ)
    (K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}) :
    parameterRound2_originalTensorGermSpace A B S W :=
  if he : 0 < epsilon ∧ epsilon ≤ 1 then
    ⟨incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell),hsm epsilon he.1 he.2 K⟩
  else 0

theorem parameterRound2_actualGermMeanReserveOperator_val
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho ell : ℝ)
    (F : Ep → M → V)
    (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (q : ℕ)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W)
    (epsilon : ℝ)
    (K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    (parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm epsilon K).val =
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) := by
  simp only [parameterRound2_actualGermMeanReserveOperator,
    dite_eq_left (show 0 < epsilon ∧ epsilon ≤ 1 from ⟨he,he1⟩)]

/-- At the threshold chosen solely from p,H,rho,Csize,Cdiff,q,loss,
the actual finite primary solver has the derived q+1 native mean residual. -/
theorem parameterRound2_actual_original_germ_mean_finite_residual
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (hp : ∀ s t, s ≤ t → ∀ K, p s K ≤ p t K)
    (ell : ℝ) (H : parameterRound2_originalTensorGermSpace A B S W)
    (rho : ℝ) (hrho : 0 < rho) (q loss : ℕ) (hq : 1 ≤ q)
    (Csize Cdiff : ℕ → ℝ → ℝ)
    (F : Ep → M → V)
    (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W) :
    let T := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      p (s+loss) K.val ≤ R → p s (T epsilon K) ≤ epsilon*Csize s R) →
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K L : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      p (s+loss) K.val ≤ R → p (s+loss) L.val ≤ R →
      p s (T epsilon K-T epsilon L) ≤ epsilon*Cdiff s R*p (s+loss) (K.val-L.val)) →
    ∀ epsilon, 0 < epsilon →
    epsilon < parameterRound2_finiteMeanThreshold p hp H rho hrho Csize Cdiff q loss hq →
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (T epsilon))^[i] H
    let R := parameterRound2_finiteMeanProfile p H Csize loss
    let C0 := fun s => max 0 (Csize s (p (s+loss) H))
    let Cd := fun i s => max 0 (Cdiff s (max (R i (s+loss)) (R (i+1) (s+loss))))
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧
    (∀ i ≤ q, ∀ s, p s (K i) ≤ R i s) ∧
    ∃ E : parameterRound2_originalTensorGermSpace A B S W,
      E.val = (fun t x => incrementsGlobalPrimaryMean F hF g (K q).val (q+2) (epsilon*ell) t x-H.val t x) ∧
      ∀ j, p j E ≤ epsilon^(q+1)*parameterRound2_finiteMeanErrorCost C0 Cd loss q j := by
  intro T hsize hdiff epsilon he he0lt K R C0 Cd
  have he1 : epsilon ≤ 1 := he0lt.le.trans
    (parameterRound2_finiteMeanThreshold_pos p hp H rho hrho Csize Cdiff q loss hq).2
  have hiter := parameterRound2_finite_mean_at_threshold p hp H rho hrho Csize Cdiff q loss hq
    T hsize hdiff epsilon he he0lt
  obtain ⟨hres,hprofile,hdom,hfinal⟩ := hiter
  let Tout := T epsilon ⟨K q,hdom⟩
  let Eout : parameterRound2_originalTensorGermSpace A B S W := K q+Tout-H
  have hTv : Tout.val = incrementsGlobalPrimaryMeanError F hF g (K q).val (q+2) (epsilon*ell) := by
    dsimp only [Tout,T,parameterRound2_actualGermMeanReserveOperator]
    simp only [dite_eq_left (show 0 < epsilon ∧ epsilon ≤ 1 from ⟨he,he1⟩)]
  refine ⟨hres,hprofile,Eout,?_,hfinal⟩
  funext t x
  change (K q).val t x+Tout.val t x-H.val t x = _
  rw [hTv]
  change (K q).val t x+(incrementsGlobalPrimaryMean F hF g (K q).val (q+2) (epsilon*ell) t x-
    (K q).val t x)-H.val t x = _
  abel

#print axioms parameterRound2_actual_original_germ_mean_finite_residual
end GlobalEmbedding.Continuation
