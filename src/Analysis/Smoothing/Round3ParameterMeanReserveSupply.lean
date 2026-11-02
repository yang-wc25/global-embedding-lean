import Smoothing.Round3ParameterMeanRawRestricted

/-! Availability of genuine primitive mean profiles on the original
symmetric C0 reserve.  Each input pair may use its proved positivity
neighborhood for analysis.  The global family, input tensor, finite solver
and actual mean operator are fixed independently of that neighborhood. -/

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

def Round3ParameterMeanRawReserveSupply
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (reserve : ℝ)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ) (T : ℕ → ℝ)
    (F : P → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (P × M)) (ell : ℝ) : Prop :=
  ∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K L : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p (s+(q+4)) L.val ≤ R →
      ∃ G : Set (P × M), ∃ hG : IsOpen G, G ⊆ W ∧
      (∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G) ∧
      Nonempty (Round3ParameterMeanRawAtlasData (Tr := Tr) A B F hF
        (round3Parameter_restrictPrimaryFamily F g G hG) K.val.val L.val.val
        (s+(q+4)) q s Rsub Lprimary reserve (Bnd s R) (Mg s) T
        G primary S (epsilon*ell) ell (Dinput s*p (s+(q+4)) (K.val-L.val)))

end GlobalEmbedding.Continuation
