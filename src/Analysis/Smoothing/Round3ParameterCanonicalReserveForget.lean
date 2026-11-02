import Smoothing.Round3ParameterCanonicalMeanReserveSupply
import Smoothing.Round3ParameterMeanReserveSupply

/-! Forgetting the canonical observer identity preserves the SAME physical
primary family and supplies the full-space mean reserve input. -/
noncomputable section
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

theorem round3Parameter_canonical_reserve_forget
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S univ))
    (H : parameterRound2_originalTensorGermSpace A B S univ) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (reserve : ℝ)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ) (T : ℕ → ℝ)
    (F : P → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (P × M)) (ell : ℝ)
    (supply : Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B S univ p H rho
      q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell) :
    Round3ParameterMeanRawReserveSupply (Tr := Tr) A B S univ p H rho q Rsub Lprimary
      reserve Bnd Mg Dinput T F hF g primary ell := by
  intro epsilon he he1 s R K L hK hL
  obtain ⟨raw,hO⟩ := supply epsilon he he1 s R K L hK hL
  exact ⟨univ,isOpen_univ,Subset.rfl,fun _ _ _ => mem_univ _,⟨raw⟩⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_canonical_reserve_forget
