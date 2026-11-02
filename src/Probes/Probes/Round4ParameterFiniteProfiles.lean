import Probes.Round3ParameterRawAtlasData
import Smoothing.ParameterRound2MeanRawGermCostIndex

/-!
# Finite transition profiles for the same physical general-parameter increment

Only the numerical transition profiles are truncated. The actual charts,
cutoffs, geometric witnesses, native pullbacks, observation domains, tensor
input, primary family and secondary choice are unchanged. Thus the same
global increment can be estimated using constants selected from finitely
many transition derivatives, even when the parameter manifold is nontrivial.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m d N c : ℕ} {P M Tr Label SubPrimary SubSecondary : Type*}
  [TopologicalSpace P] [TopologicalSpace M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

/-- Reuse every physical witness and replace only unused higher transition
profile values by zero. Host and inverse transitions are read through
`nSolve + 1`; observation transitions are read through `j + 2`. -/
def round4ParameterRawAtlasDataPrefix
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hj : j ≤ nSolve)
    (reserve Bnd Mg Kcut : ℝ) (T Tinv Tobs : ℕ → ℝ)
    (W : Set (P × M)) (primary : Label → Set (P × M))
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (ell delta tau Delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
    (data : Round3ParameterRawAtlasData (Tr := Tr) A B F hF g input inputbar
      nInput nSolve j q Rsub Lprimary Rsecondary reserve Bnd Mg Kcut T Tinv Tobs
      W primary S ell delta tau Delta choice) :
    Round3ParameterRawAtlasData (Tr := Tr) A B F hF g input inputbar
      nInput nSolve j q Rsub Lprimary Rsecondary reserve Bnd Mg Kcut
      (parameterRound2_numericProfilePrefix (nSolve+1) T)
      (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
      (parameterRound2_numericProfilePrefix (j+2) Tobs)
      W primary S ell delta tau Delta choice := by
  let raw' (b : Fin c) : ActualOriginalSecondaryRawData (Tr := Tr)
      (fun t => F ((B b).symm t)) (fun t => hF ((B b).symm t))
      (round3ParameterNativePrimary F g (B b))
      (fun t => input ((B b).symm t)) (fun t => inputbar ((B b).symm t))
      nInput nSolve j q Rsub Lprimary reserve Bnd Mg Kcut
      (parameterRound2_numericProfilePrefix (nSolve+1) T)
      (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
      (round3ParameterNativeDomain (B b) W)
      (fun ν => round3ParameterNativeDomain (B b) (primary ν))
      ell delta tau Delta (round3ParameterNativeChoices choice (B b)) := {
    data.raw b with
    hostProfiles := by
      intro r a
      exact { (data.raw b).hostProfiles r a with
        hphib := by
          intro nu beta k hk hks z hz
          simpa only [parameterRound2_numericProfilePrefix,ite_eq_left hks] using
            ((data.raw b).hostProfiles r a).hphib nu beta k hk hks z hz }
    inverseJets := by
      intro r a host transition k hk hks z hz
      simpa only [parameterRound2_numericProfilePrefix,ite_eq_left hks] using
        (data.raw b).inverseJets r a k hk hks z hz }
  exact {
    raw := raw'
    observationDomain := data.observationDomain
    observation := fun i => {
      data.observation i with
      profiles := {
        (data.observation i).profiles with
        hphib := by
          intro nu beta k hk hkj z hz
          have hks : k ≤ nSolve+1 := hkj.trans (Nat.add_le_add_right hj 1)
          simpa only [parameterRound2_numericProfilePrefix,ite_eq_left hks] using
            (data.observation i).profiles.hphib nu beta k hk hkj z hz }
      transitionJets := by
        intro r a z hz k hk hkj
        simpa only [parameterRound2_numericProfilePrefix,ite_eq_left hkj] using
          (data.observation i).transitionJets r a z hz k hk hkj } }

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterRawAtlasDataPrefix
