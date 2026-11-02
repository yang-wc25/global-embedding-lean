import Probes.ActualSecondaryObservedPhysicalIdentity

/-!
# Actual supported secondary error jets in an observation chart

The input is primitive forcing/geometry/chart data for the SAME constructed
supported wave. Source bounds, finite-polynomial residual, physical rows,
real tensor assembly, genuine coordinate identity and both Jacobian factors
are all consumed internally. The output is the literal metric variation of
that supported wave minus its literal transported forcing.
-/

noncomputable section
open Manifold Set Filter Function GlobalEmbedding.Paper
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

private local instance observedTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance observedTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance observedTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem actual_observed_secondary_physical_error_weighted_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (d : ActualSecondaryPieceData (I := 𝓙) (m := m) F hF n j ell Mg CH delta W)
    (chart : Ep → OpenPartialHomeomorph M D) (hc : d.c = fun p x => (chart p).symm x)
    (hchart : ∀ p, chart p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hOt : ∀ z ∈ d.chart.target, z.2 ∈ (chart z.1).target)
    (hinj : ∀ z ∈ d.chart.target,
      Function.Injective (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((chart z.1).symm z.2)))
    (hfree : ∀ z ∈ d.chart.target,
      let beta := incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm z.2 a.succ)
      (beta.comp beta.adjoint).IsInvertible)
    (hRsymm : ∀ z ∈ d.chart.target, ∀ i j, d.hR z i j = d.hR z j i)
    (hIsymm : ∀ z ∈ d.chart.target, ∀ i j, d.hI z i j = d.hI z j i)
    (kappa : X → Ep × M) (O : Set X) (hO : IsOpen O)
    (hsource : MapsTo kappa O d.chart.source)
    (hfirst : ∀ z ∈ O, (kappa z).1 = z.1)
    (htransition : ContDiffOn ℝ ∞ (d.chart ∘ kappa) O)
    (tau : ℝ) (length : ℕ) (hbudget : j+1+length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH)
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (z : X) (hz : z ∈ O)
    (hsample : d.chart (kappa z) ∈ d.sample)
    (htransitionb : ∀ i, 1 ≤ i → i ≤ j+1 →
      ell ^ (i-1) * ‖iteratedFDeriv ℝ i (d.chart ∘ kappa) z‖ ≤ T i) :
    ContDiffOn ℝ ∞ (actualObservedSecondaryPhysicalError F hF d kappa tau length) O ∧
    ∀ s ≤ j, tau ^ s * ‖iteratedFDeriv ℝ s
      (actualObservedSecondaryPhysicalError F hF d kappa tau length) z‖ ≤
      actualFastTensorChartTransferCost T s * actualSecondaryPhysicalCost m N n length j Mg CH *
        (tau / ell) ^ length * delta ^ 2 := by
  let B := actualRemodulatedPhysicalTensor
    (actualSecondaryPhysicalError F hF chart d.hR d.hI tau length) (fun y : X => y.2 0) tau
  let K := actualSecondaryPhysicalCost m N n length j Mg CH * (tau / ell) ^ length * delta ^ 2
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (actualSecondaryPhysicalCost_nonneg m N n length j Mg CH hMg hCH)
      (pow_nonneg (div_nonneg htau.le hell.le) length)) (sq_nonneg delta)
  obtain ⟨hB, hb⟩ := actual_constructed_secondary_physical_tensor_jets F hF n j ell Mg CH delta W d
    chart hc hchart hOt hinj hfree hRsymm hIsymm tau length (by omega)
    hell hell1 htau htaul hMg hCH
  obtain ⟨hp, hpb⟩ := actual_fast_joint_tensor_chart_transfer T hT j (d.chart ∘ kappa) B
    O d.chart.target hO d.chart.open_target htransition hB
    (fun y hy => d.chart.map_source (hsource hy)) z hz tau ell K htau htaul hK
    (fun i hi => hb i hi _ hsample) htransitionb
  have he := actual_observed_secondary_physical_error_eq F hF d chart hc hchart hOt kappa O hO
    hsource hfirst htransition tau length hbudget hell hell1 htau htaul hMg hCH
  refine ⟨hp.congr he, ?_⟩
  intro s hs
  have hps := (actual_fast_joint_tensor_chart_transfer T hT s (d.chart ∘ kappa) B
    O d.chart.target hO d.chart.open_target htransition hB
    (fun y hy => d.chart.map_source (hsource hy)) z hz tau ell K htau htaul hK
    (fun i hi => hb i (hi.trans hs) _ hsample)
    (fun i hi his => htransitionb i hi (by omega))).2
  have hg : actualObservedSecondaryPhysicalError F hF d kappa tau length =ᶠ[𝓝 z]
      (fun y => (B (d.chart (kappa y))).bilinearComp
        (actualJointSpatialJacobian (d.chart ∘ kappa) y)
        (actualJointSpatialJacobian (d.chart ∘ kappa) y)) := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact he hy
  rw [(hg.iteratedFDeriv ℝ s).eq_of_nhds]
  exact hps.trans_eq (by dsimp only [K]; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_observed_secondary_physical_error_weighted_jets
