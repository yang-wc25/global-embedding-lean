import Probes.Round3ParameterNativeFamily

/-! Actual native raw profiles for the canonical pullbacks of one global
family.  The physical domain, input tensor, phase labels and secondary choices
are shared before any observation order.  The record contains the established
primitive geometry/profile/observer data, with no estimate or regularity field
for the output increment, its mean, or its metric error. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {P Q M : Type*} [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace M]

def round3ParameterNativeDomain (B : OpenPartialHomeomorph P Q) (W : Set (P × M)) : Set (Q × M) :=
  {z | z.1 ∈ B.target ∧ (B.symm z.1,z.2) ∈ W}

section Data
variable {m d N c : ℕ} {Tr Label SubPrimary SubSecondary : Type*}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

structure Round3ParameterRawAtlasData
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ)
    (reserve Bnd Mg Kcut : ℝ) (T Tinv Tobs : ℕ → ℝ)
    (W : Set (P × M)) (primary : Label → Set (P × M))
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (ell delta tau Delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m) where
  raw : ∀ b : Fin c,
    ActualOriginalSecondaryRawData (Tr := Tr)
      (fun t => F ((B b).symm t)) (fun t => hF ((B b).symm t))
      (round3ParameterNativePrimary F g (B b))
      (fun t => input ((B b).symm t)) (fun t => inputbar ((B b).symm t))
      nInput nSolve j q Rsub Lprimary reserve Bnd Mg Kcut T Tinv
      (round3ParameterNativeDomain (B b) W) (fun ν => round3ParameterNativeDomain (B b) (primary ν))
      ell delta tau Delta (round3ParameterNativeChoices choice (B b))
  observationDomain : Fin A.count × Fin c → Set (Ep × D)
  observation : ∀ i : Fin A.count × Fin c,
    ActualOriginalSecondaryObservationData (raw i.2) Tobs Rsecondary (A.chart i.1)
      (observationDomain i) ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)

end Data
end GlobalEmbedding.Continuation
