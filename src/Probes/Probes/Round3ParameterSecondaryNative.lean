import Probes.Round3ParameterSecondaryConstruction
import Probes.Round3ParameterPrimaryNative

/-! The general parameter increment specializes to exactly the original actual
primary-plus-secondary finite map, including both forcing Jacobians. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Label SubPrimary SubSecondary : Type*} [Fintype Label] [DecidableEq Label]
  [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def Round3ParameterSecondaryChoice.toNative (c : Round3ParameterSecondaryChoice Ep M m) :
    ActualOriginalSecondaryChoice Ep M m where
  host := c.host
  chart := c.chart
  c := c.c
  cutoff := c.cutoff

def Round3ParameterSecondaryChoice.ofNative (c : ActualOriginalSecondaryChoice Ep M m) :
    Round3ParameterSecondaryChoice Ep M m where
  host := c.host
  chart := c.chart
  c := c.c
  cutoff := c.cutoff

variable (F : Ep → M → (EuclideanSpace ℝ (Fin N))) (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,(EuclideanSpace ℝ (Fin N))) ∞ (F p))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (m := m) (Λ := Label) (Β := SubPrimary) F)
  (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (length : ℕ) (tau delta : ℝ)

theorem round3ParameterSecondary_native_piece
    (r : (Label × Label) × Fin 4) (c : Round3ParameterSecondaryChoice Ep M m) :
    actualOriginalSecondaryPiece F hF (g.toNative F) input length tau delta r c.toNative =
      round3ParameterSecondaryPiece (SubPrimary := SubPrimary) F hF g input length tau delta r c := rfl

theorem round3ParameterSecondary_native_sum
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice Ep M m) :
    actualOriginalSecondarySum F hF (g.toNative F) input length tau delta
      (fun r a => (choice r a).toNative) =
      round3ParameterSecondarySum (SubPrimary := SubPrimary) F hF g input length tau delta choice := rfl

theorem round3Parameter_native_increment
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice Ep M m) :
    actualOriginalIncrementMap F hF (g.toNative F) input length tau delta
      (fun r a => (choice r a).toNative) =
      round3ParameterIncrementMap (SubPrimary := SubPrimary) F hF g input length tau delta choice := rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_native_increment
