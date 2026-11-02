import Smoothing.Round3ParameterCanonicalMeanReserveSupply
import Probes.ActualRawProfileBudgets

/-! The actual canonical primary raw supply is evaluated at the SAME global
input twice. Its original observer domains are retained, and the difference
budget becomes exactly zero. The input reserve and high-order bound are the
independent mean-iterate certificates, not conclusions of secondary repair. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M P Tr Λ Β : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_canonical_final_raw
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (reserve : ℝ)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ) (T : ℕ → ℝ)
    (F : P → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (P × M)) (ell : ℝ)
    (supply : Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B S W p H rho
      q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell)
    (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (s : ℕ) (R Bfinal Mfinal : ℝ)
    (hBnd : Bnd s R ≤ Bfinal) (hMg : Mg s ≤ Mfinal)
    (K : parameterRound2_originalTensorGermSpace A B S W)
    (hK : p 0 (K-H) < rho) (hKR : p (s+(q+4)) K ≤ R) :
    Nonempty (∀ i : Fin A.count × Fin c,
      ParameterRound2GlobalMeanRawProfiles (Tr := Tr) (s+(q+4)) (q+2) s Rsub Lprimary
        reserve Bfinal Mfinal T
        (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
        (round3ParameterNativePrimary F
          (round3Parameter_restrictPrimaryFamily F g univ isOpen_univ) (B i.2))
        (fun t => K.val ((B i.2).symm t)) (fun t => K.val ((B i.2).symm t))
        (round3ParameterNativeDomain (B i.2) (univ : Set (P × M)))
        (fun nu => round3ParameterNativeDomain (B i.2) (primary nu))
        (A.chart i.1)
        (actualRawObserverOpen (A.chart i.1) (round3ParameterNativeDomain (B i.2) (univ : Set (P × M))))
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i) (epsilon*ell) ell 0) := by
  obtain ⟨out,hO⟩ := supply epsilon he he1 s R ⟨K,hK⟩ ⟨K,hK⟩ hKR hKR
  refine ⟨fun i => ?_⟩
  have raw := out.raw i
  have hOi := congrFun hO i
  rw [hOi] at raw
  simp only [sub_self,map_zero,mul_zero] at raw
  exact actual_raw_profiles_enlarge_budgets (s+(q+4)) (q+2) s Rsub Lprimary
    reserve (Bnd s R) (Mg s) Bfinal Mfinal T hBnd hMg _ _ _ _ _ _ _ _ _ _ _ _ _ raw

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_canonical_final_raw
