import Probes.Round3ParameterSecondaryConstruction
import Smoothing.ParameterRound2ActualModeLocality

/-! Locality of the existing inhomogeneous secondary solver in its actual
forcing.  Only open-domain equality is needed.  Values of inverse charts
outside their targets are never constrained to preserve a parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Filter Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Source" => Fin (m+1) → Fin (m+1) → ℝ
variable (F : P → M → (EuclideanSpace ℝ (Fin N))) (hF : ∀ p, ContMDiff I 𝓘(ℝ,(EuclideanSpace ℝ (Fin N))) ∞ (F p))
  (c : P → (EuclideanSpace ℝ (Fin (m+1))) → M) (hR hI kR kI : P × (EuclideanSpace ℝ (Fin (m+1))) → (Fin (m+1) → Fin (m+1) → ℝ))
  (p : P) (O : Set (EuclideanSpace ℝ (Fin (m+1))))
  (hRk : EqOn (fun x => hR (p,x)) (fun x => kR (p,x)) O)
  (hIk : EqOn (fun x => hI (p,x)) (fun x => kI (p,x)) O)
include hRk hIk

theorem round3ParameterSecondary_source_eqOn :
    EqOn (fun x => actualSecondaryComplexSource F hF c hR hI (p,x))
      (fun x => actualSecondaryComplexSource F hF c kR kI (p,x)) O := by
  intro x hx
  simp only [actualSecondaryComplexSource, incrementsModeSource,
    incrementsModeTransverseSource, hRk hx, hIk hx]

theorem round3ParameterSecondary_solution_eqOn (hO : IsOpen O) (tau : ℝ) (length : ℕ) :
    EqOn (actualSecondarySolution F hF c hR hI tau length p)
      (actualSecondarySolution F hF c kR kI tau length p) O := by
  exact parameterRound2_actual_modeSum_eqOn
    (incrementsModeComplexFirstOrderA (F p) (hF p) (c p))
    (incrementsModeComplexFirstOrderB (F p) (hF p) (c p))
    ((tau:ℂ)/Complex.I) length _ _ O hO
    (round3ParameterSecondary_source_eqOn F hF c hR hI kR kI p O hRk hIk)

theorem round3ParameterSecondary_realChannel_eqOn (hO : IsOpen O) (tau : ℝ) (length : ℕ) :
    EqOn (fun x => actualSecondaryRealChannel F hF c hR hI tau length (p,x))
      (fun x => actualSecondaryRealChannel F hF c kR kI tau length (p,x)) O := by
  intro x hx
  have hu := round3ParameterSecondary_solution_eqOn F hF c hR hI kR kI p O hRk hIk hO tau length
  have he : (incrementsModeRealPart ∘ actualSecondarySolution F hF c hR hI tau length p) =ᶠ[𝓝 x]
      (incrementsModeRealPart ∘ actualSecondarySolution F hF c kR kI tau length p) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact congrArg incrementsModeRealPart (hu hy)
  simp only [actualSecondaryRealChannel, incrementsModeFullReconstruction]
  rw [parameterRound2_actual_reconstruction_germ (F p) (hF p) (c p) _ _ x he]
  simp only [incrementsModeTransverseSource, hRk hx]

theorem round3ParameterSecondary_imagChannel_eqOn (hO : IsOpen O) (tau : ℝ) (length : ℕ) :
    EqOn (fun x => actualSecondaryImagChannel F hF c hR hI tau length (p,x))
      (fun x => actualSecondaryImagChannel F hF c kR kI tau length (p,x)) O := by
  intro x hx
  have hu := round3ParameterSecondary_solution_eqOn F hF c hR hI kR kI p O hRk hIk hO tau length
  have he : (incrementsModeImagPart ∘ actualSecondarySolution F hF c hR hI tau length p) =ᶠ[𝓝 x]
      (incrementsModeImagPart ∘ actualSecondarySolution F hF c kR kI tau length p) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact congrArg incrementsModeImagPart (hu hy)
  simp only [actualSecondaryImagChannel, incrementsModeFullReconstruction]
  rw [parameterRound2_actual_reconstruction_germ (F p) (hF p) (c p) _ _ x he]
  simp only [incrementsModeTransverseSource, hIk hx]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterSecondary_realChannel_eqOn
#print axioms GlobalEmbedding.Continuation.round3ParameterSecondary_imagChannel_eqOn
