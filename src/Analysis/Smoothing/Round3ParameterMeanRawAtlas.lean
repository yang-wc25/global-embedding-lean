import Probes.Round3ParameterRawAtlasData
import Smoothing.ParameterRound2MeanRawArrayIndex

/-! Primitive mean profiles in every actual parameter chart, for one global
family and one pair of global tensor inputs.  The sample is precisely the
original source-first sample pulled through its linear model equivalence.
Parameter charts are already included in the primitive functions; there is
no extra linearized parameter map and no estimate for the output mean. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Manifold
open scoped ContDiff Topology
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

structure Round3ParameterMeanRawAtlasData
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (n q j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ)
    (W : Set (P × M)) (primary : Λ → Set (P × M))
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (tau ell Delta : ℝ) where
  observationDomain : Fin A.count × Fin c → Set (Ep × D)
  target : ∀ i z, z ∈ observationDomain i → z.2 ∈ (A.chart i.1).target
  raw : ∀ i : Fin A.count × Fin c,
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n (q+2) j Rsub Lprimary reserve Bnd Mg T
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2))
      (fun t => input ((B i.2).symm t)) (fun t => inputbar ((B i.2).symm t))
      (round3ParameterNativeDomain (B i.2) W)
      (fun ν => round3ParameterNativeDomain (B i.2) (primary ν))
      (A.chart i.1) (observationDomain i) ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)
      tau ell Delta

end GlobalEmbedding.Continuation
