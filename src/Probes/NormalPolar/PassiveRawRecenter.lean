import Smoothing.Round3ParameterCanonicalMeanReserveSupply

/-! Recenter the same actual canonical raw supplier on a nearby original
tensor, using half of its proved C0 reserve. The actual input tensors,
fields, domains and all raw budgets remain unchanged; only the proofs of
membership in the original reserve ball are transported. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

theorem passiveRaw_recenter_ball {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : Seminorm ℝ X) (H₀ H₁ K : X) (rho : ℝ)
    (hCenter : p (H₁-H₀) ≤ rho/2) (hK : p (K-H₁) < rho/2) :
    p (K-H₀) < rho := by
  have hEq : K-H₀ = (K-H₁)+(H₁-H₀) := by abel
  have ht : p (K-H₀) ≤ p (K-H₁)+p (H₁-H₀) := by
    rw [hEq]
    exact map_add_le_add p _ _
  linarith

variable {m d N c : ℕ} {M P Tr Λ Β : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

theorem round3Parameter_canonical_supply_recenter
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H₀ H₁ : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (reserve : ℝ)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ) (T : ℕ → ℝ)
    (F : P → M → V) (hF : ∀ t, ContMDiff IM 𝓘(ℝ,V) ∞ (F t))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (P × M)) (ell : ℝ)
    (supply : Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B S W p H₀ rho
      q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell)
    (hCenter : p 0 (H₁-H₀) ≤ rho/2) :
    Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B S W p H₁ (rho/2)
      q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell := by
  intro epsilon he he1 s bound K L hK hL
  let K₀ : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H₀) < rho} :=
    ⟨K.val,passiveRaw_recenter_ball (p 0) H₀ H₁ K.val rho hCenter K.property⟩
  let L₀ : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H₀) < rho} :=
    ⟨L.val,passiveRaw_recenter_ball (p 0) H₀ H₁ L.val rho hCenter L.property⟩
  exact supply epsilon he he1 s bound K₀ L₀ hK hL

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveRaw_recenter_ball
#print axioms GlobalEmbedding.Continuation.round3Parameter_canonical_supply_recenter
