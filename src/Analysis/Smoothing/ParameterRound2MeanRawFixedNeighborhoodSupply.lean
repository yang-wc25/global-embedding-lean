import Smoothing.ParameterRound2MeanRawGermReserveSupply

/-! Concrete LOCAL raw-profile availability on the original symmetric reserve.
The actual positivity neighborhood may depend on each pair of native inputs.
The actual global family is unchanged: only its charts are restricted, and
the same original mean is recovered by the proved exact restriction identities.
This predicate contains only original primitive conditions and bounds of
primitive geometry, cutoffs, actual input coordinates and their differences.
It contains no estimate of T, the mean, or a residual. -/

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

def ParameterRound2MeanRawFixedNeighborhoodSupply
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (reserve : ℝ)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ) (T : ℕ → ℝ)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (Ep × M)) (ell : ℝ) : Prop :=
  ∀ (K L : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      ∃ G : Set (Ep × M), ∃ hG : IsOpen G, G ⊆ W ∧
      (∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G) ∧
      ∃ Obs : Fin A.count × Fin c → Set X,
      (∀ i, Obs i ⊆ (B i.2).source ×ˢ (A.chart i.1).target) ∧
      ∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R,
      p (s+(q+4)) K.val ≤ R → p (s+(q+4)) L.val ≤ R →
      Nonempty (∀ i : Fin A.count × Fin c, ParameterRound2GlobalMeanRawProfiles (Tr := Tr) (s+(q+4)) (q+2) s Rsub Lprimary
        reserve (Bnd s R) (Mg s) T F hF (parameterRound2_restrictPrimaryFamily F g G hG) K.val.val L.val.val G primary (A.chart i.1)
        (Obs i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i))
        (epsilon*ell) ell (Dinput s*p (s+(q+4)) (K.val-L.val)))


theorem parameterRound2_fixed_neighborhood_supply_to_germ_supply
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (reserve : ℝ)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ) (T : ℕ → ℝ)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (Ep × M)) (ell : ℝ)
    (h : ParameterRound2MeanRawFixedNeighborhoodSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
      Bnd Mg Dinput T F hF g primary ell) :
    ParameterRound2MeanRawGermReserveSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
      Bnd Mg Dinput T F hF g primary ell := by
  intro epsilon he he1 s R K L hK hL
  obtain ⟨G,hG,hGW,hSG,Obs,hObs,hraw⟩ := h K L
  exact ⟨G,hG,hGW,hSG,Obs,hObs,hraw epsilon he he1 s R hK hL⟩

#print axioms parameterRound2_fixed_neighborhood_supply_to_germ_supply
end GlobalEmbedding.Continuation
