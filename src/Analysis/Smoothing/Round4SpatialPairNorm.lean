import Smoothing.Round4ClosedParameterAtlas
import Smoothing.ParameterFiniteGeometry
import Smoothing.ParameterRound2CompactPair

/-!
# Literal spatial-two-jet pair norm on the same original chart family

This is exactly the pre-existing parameterOriginalPairWeighted expression,
extended to chart families by removing its unused global-cover proof. The
frozen total-joint norm is unchanged and is not identified with this norm.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation

/-- Compact evaluation gives finite actual spatial-packet norms before toReal. -/
theorem round4SpatialWeighted_finite_of_compact
    {ι : Type*} [Fintype ι] {n d q : ℕ}
    (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hS : ∀ i, IsCompact (S i))
    (hSO : ∀ i, S i ⊆ O i) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (m : ℕ) (t : ℝ) : parameterSpatialWeighted (n := n) (d := d) m t f O S ≠ ⊤ :=
  parameterRound2_paperAtlasWeighted_finite_of_compact (parameterSpatialPacket f)
    (fun iw => O iw.1) (fun iw => S iw.1) (fun iw => S iw.1)
    (fun iw => hO iw.1) (fun iw => hS iw.1) (fun _ => Subset.rfl)
    (fun iw => hSO iw.1)
    (fun iw => parameterSpatialJet_contDiffOn (hO iw.1) (hf iw.1) iw.2) 0 m t

variable {n d q pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin q)

def round4ParameterSpatialPairWeighted
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (u : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (m : ℕ) (t : ℝ) (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ)) : ℝ≥0∞ :=
  parameterSpatialWeighted (n := n) (d := d) m t (incrementsOriginalMapCoordinates A B.chart u)
    (incrementsOriginalDifferentiation A B.chart) S +
  paperAtlasWeighted 0 m t (incrementsOriginalTensorCoordinates A B.chart H)
    (incrementsOriginalDifferentiation A B.chart) S

theorem round4ParameterSpatialPairWeighted_eq_original
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hcover : ∀ p, ∃ i, p ∈ B.inner i) (u : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (m : ℕ) (t : ℝ) (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ)) :
    round4ParameterSpatialPairWeighted A B u H m t S =
      parameterOriginalPairWeighted A (round4ClosedParameterAtlas B hcover) u H m t S := rfl

theorem round4ParameterSpatialPairWeighted_finite
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin pcount → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B.chart i).target)
    (u : P × M → Ey)
    (hu : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
      (incrementsOriginalDifferentiation A B.chart i))
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i)) (j : ℕ) (t : ℝ) :
    round4ParameterSpatialPairWeighted A B u H j t
      (incrementsOriginalEvaluation A B.chart Omega Q univ) ≠ ⊤ := by
  let O := incrementsOriginalDifferentiation A B.chart
  let S := incrementsOriginalEvaluation A B.chart Omega Q univ
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B.chart
  have hS : ∀ i, IsCompact (S i) := parameterRound2_originalEvaluation_univ_compact
    A B.chart Omega Q hOmega hQ hOmegaTarget hQTarget
  have hSO : ∀ i, S i ⊆ O i := fun _ _ hy => hy.1
  exact ENNReal.add_ne_top.mpr
    ⟨round4SpatialWeighted_finite_of_compact _ O S hO hS hSO hu j t,
     parameterRound2_paperAtlasWeighted_finite_of_compact _ O S S hO hS
       (fun _ => Subset.rfl) hSO hH 0 j t⟩

#print axioms round4ParameterSpatialPairWeighted_eq_original
#print axioms round4ParameterSpatialPairWeighted_finite
end GlobalEmbedding.Continuation
