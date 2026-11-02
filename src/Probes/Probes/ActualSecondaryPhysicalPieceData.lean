import Probes.ActualSecondaryObservedPhysicalJets
import Probes.ActualSecondaryObservedSupport

/-!
# Primitive geometric data for physical secondary pieces

This records actual charts, immersion and transverse Gram admissibility for
the same previously constructed piece. It has no residual, displacement or
error-budget fields. The Gram condition is supplied by the original good
phase theorem in the geometric producer, rather than a new final-target
assumption. All outputs remain the original supported wave and metric error.
-/

noncomputable section
open Manifold Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)

structure ActualSecondaryPhysicalPieceData
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M)) where
  base : ActualSecondaryPieceData (I := 𝓙) (m := m) F hF n j ell Mg CH delta W
  spatialChart : Ep → OpenPartialHomeomorph M D
  coordinate : base.c = fun p x => (spatialChart p).symm x
  maximal : ∀ p, spatialChart p ∈ IsManifold.maximalAtlas 𝓙 ∞ M
  target : ∀ z ∈ base.chart.target, z.2 ∈ (spatialChart z.1).target
  immersion : ∀ z ∈ base.chart.target,
    Function.Injective (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((spatialChart z.1).symm z.2))
  gram : ∀ z ∈ base.chart.target,
    let beta := incrementsTransversePairing (F z.1) (hF z.1) ((spatialChart z.1).symm z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (spatialChart z.1).symm z.2 a.succ)
    (beta.comp beta.adjoint).IsInvertible
  symmetricR : ∀ z ∈ base.chart.target, ∀ i j, base.hR z i j = base.hR z j i
  symmetricI : ∀ z ∈ base.chart.target, ∀ i j, base.hI z i j = base.hI z j i

theorem actual_secondary_physical_piece_observation_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (d : ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (kappa : X → Ep × M) (O : Set X) (hO : IsOpen O)
    (hsource : MapsTo kappa O d.base.chart.source)
    (hfirst : ∀ z ∈ O, (kappa z).1 = z.1)
    (htransition : ContDiffOn ℝ ∞ (d.base.chart ∘ kappa) O)
    (tau : ℝ) (length : ℕ) (hbudget : j+1+length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH)
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (z : X) (hz : z ∈ O)
    (hsample : d.base.chart (kappa z) ∈ d.base.sample)
    (htransitionb : ∀ i, 1 ≤ i → i ≤ j+1 →
      ell ^ (i-1) * ‖iteratedFDeriv ℝ i (d.base.chart ∘ kappa) z‖ ≤ T i) :
    ContDiffOn ℝ ∞ (actualObservedSecondaryPhysicalError F hF d.base kappa tau length) O ∧
    ∀ s ≤ j, tau ^ s * ‖iteratedFDeriv ℝ s
      (actualObservedSecondaryPhysicalError F hF d.base kappa tau length) z‖ ≤
      actualFastTensorChartTransferCost T s * actualSecondaryPhysicalCost m N n length j Mg CH *
        (tau / ell) ^ length * delta ^ 2 := by
  exact actual_observed_secondary_physical_error_weighted_jets F hF n j ell Mg CH delta W d.base
    d.spatialChart d.coordinate d.maximal d.target d.immersion d.gram d.symmetricR d.symmetricI
    kappa O hO hsource hfirst htransition tau length hbudget hell hell1 htau htaul hMg hCH
    T hT z hz hsample htransitionb

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_physical_piece_observation_jets
