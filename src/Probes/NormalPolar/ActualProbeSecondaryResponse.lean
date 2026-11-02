import Probes.ActualSecondaryCompleteMetricJets
import Probes.ActualSecondaryModulation
import NormalPolar.OriginalProbeScales

/-!
# Actual complete secondary waves and their native probe responses

The observation record contains only the original physical pieces, actual
chart transitions, samples, relative supports and active multiplicities.
It contains no bound for the completed secondary sum or either response.
The same full signed ordered array is reconstructed and summed before its
native parameter derivative and spatial Hessian are estimated.

The probe parameter must be part of this actual joint family.  A separate
external parameter in a chosen piece array is not silently differentiated.
-/

noncomputable section
open Set Function Filter Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N n j : ℕ} {Ep M Label Sub Y : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]

/-- Primitive observer data for the SAME complete physical secondary array.
Every transition profile is required only on its actual active support. -/
structure ActualSecondaryProbeObservation
    (F : Ep → M → EuclideanSpace ℝ (Fin N))
    (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
    {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] where
  kappa : Y → Ep × M
  domain : Set Y
  sample : Set Y
  domain_open : IsOpen domain
  sample_subset : sample ⊆ domain
  smooth : ContMDiffOn 𝓘(ℝ,Y)
    ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) ∞ kappa domain
  mapsTo : MapsTo kappa domain W
  primarySupport : Label → Set (Ep × M)
  primary_support : ∀ rec a, (data rec a).base.support ⊆
    primarySupport rec.val.1.1 ∩ primarySupport rec.val.1.2
  localDomain : ActualSecondarySignedRecord Label → Sub → Set Y
  local_open : ∀ rec a, IsOpen (localDomain rec a)
  active_local : ∀ rec a, sample ∩ kappa ⁻¹' (data rec a).base.support ⊆ localDomain rec a
  source : ∀ rec a, MapsTo kappa (localDomain rec a) (data rec a).base.chart.source
  transition_smooth : ∀ rec a,
    ContDiffOn ℝ ∞ ((data rec a).base.chart ∘ kappa) (localDomain rec a)
  transitionCost : ℕ → ℝ
  transitionCost_nonneg : ∀ k, 0 ≤ transitionCost k
  active_sample : ∀ rec a y, y ∈ sample ∩ kappa ⁻¹' (data rec a).base.support →
    (data rec a).base.chart (kappa y) ∈ (data rec a).base.sample
  transition_bound : ∀ rec a y, y ∈ sample ∩ kappa ⁻¹' (data rec a).base.support →
    ∀ k, 1 ≤ k → k ≤ j →
      ell ^ (k-1) * ‖iteratedFDeriv ℝ k ((data rec a).base.chart ∘ kappa) y‖ ≤ transitionCost k
  primaryCount : ℕ
  secondaryCount : ℕ
  primary_count : ∀ y ∈ sample,
    (Finset.univ.filter (fun l => kappa y ∈ primarySupport l)).card ≤ primaryCount
  secondary_count : ∀ rec : ActualSecondarySignedRecord Label, ∀ y ∈ sample,
    (Finset.univ.filter (fun a => kappa y ∈ (data rec a).base.support)).card ≤ secondaryCount

namespace ActualSecondaryProbeObservation
variable {F : Ep → M → EuclideanSpace ℝ (Fin N)}
  {hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p)}
  {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
  {data : ActualSecondarySignedRecord Label → Sub →
    ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W}

def wave (obs : ActualSecondaryProbeObservation F hF data Y) (tau : ℝ) (length : ℕ) :
    Y → EuclideanSpace ℝ (Fin N) :=
  actualConstructedSecondarySum F hF (fun rec a => (data rec a).base) tau length ∘ obs.kappa

def cost (obs : ActualSecondaryProbeObservation F hF data Y) (length : ℕ) : ℝ :=
  actualConstructedSecondaryWaveBudget m N n j length obs.primaryCount obs.secondaryCount
    Mg CH obs.transitionCost

theorem cost_nonneg (obs : ActualSecondaryProbeObservation F hF data Y)
    (length : ℕ) (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) : 0 ≤ obs.cost length := by
  have hp := actualFastChartTransferPrefix_nonneg obs.transitionCost obs.transitionCost_nonneg j
  have hc := actualSecondaryForcedWaveCost_nonneg m N n length j Mg CH hMg hCH
  unfold cost actualConstructedSecondaryWaveBudget
  positivity

/-- Global smoothness follows from the actual supported physical pieces,
so no arbitrary global extension of an inactive phase is differentiated. -/
theorem wave_smooth (obs : ActualSecondaryProbeObservation F hF data Y)
    (tau : ℝ) (length : ℕ) (hW : IsOpen W) :
    ContDiffOn ℝ ∞ (obs.wave tau length) obs.domain := by
  change ContDiffOn ℝ ∞ (fun z => actualSecondaryRefinedNonzeroSum
    (actualConstructedSecondaryFamily F hF (fun rec a => (data rec a).base) tau length)
      (obs.kappa z)) obs.domain
  rw [actual_secondary_refined_sum_eq_records]
  apply ContDiffOn.sum
  intro rec hr
  apply ContDiffOn.sum
  intro a _
  have hq := (Finset.mem_filter.mp hr).2
  have hm := (((data ⟨rec,hq⟩ a).base.wave_regular tau length hW).1.comp
    obs.smooth obs.mapsTo).contDiffOn
  simpa only [actualConstructedSecondaryFamily,dif_pos hq,Function.comp_def] using hm

/-- This is an output of the finite solver, all signed support sums and
actual chart transfer; it is not a field of the observation record. -/
theorem weighted_jets (obs : ActualSecondaryProbeObservation F hF data Y)
    (tau : ℝ) (length : ℕ) (hbudget : j+1+length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) (hW : IsOpen W) :
    ∀ k ≤ j, ∀ y ∈ obs.sample,
      tau ^ k * ‖iteratedFDeriv ℝ k (obs.wave tau length) y‖ ≤ obs.cost length * delta ^ 2 := by
  exact (actual_constructed_secondary_sum_weighted_jets F hF
    (fun rec a => (data rec a).base) tau length hbudget hell hell1 htau htaul hMg hCH hW
    obs.primarySupport obs.primary_support obs.kappa obs.domain obs.sample obs.domain_open
    obs.sample_subset obs.smooth.continuousOn obs.mapsTo obs.localDomain obs.local_open
    obs.active_local obs.source obs.transition_smooth obs.transitionCost obs.transitionCost_nonneg
    obs.active_sample obs.transition_bound obs.primaryCount obs.secondaryCount
    obs.primary_count obs.secondary_count).2

section Native
variable {U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance secondaryProbeBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance secondaryProbeBilinearNormed :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance secondaryProbeBilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedSpace
private local instance secondaryProbeResponseSemi :
    SeminormedAddCommGroup (U →L[ℝ] E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance secondaryProbeResponseNormed :
    NormedAddCommGroup (U →L[ℝ] E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Native parameter value and native parameter/spatial-Hessian bounds for
the same complete secondary sum. The parameter is the actual first factor
of the observer; every signed mixed term is present. -/
theorem native_responses (obs : ActualSecondaryProbeObservation F hF data (U × E))
    (tau : ℝ) (length : ℕ) (hj : 3 ≤ j) (hbudget : j+1+length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) (hW : IsOpen W)
    (z : U × E) (hz : z ∈ obs.sample) :
    ‖fderiv ℝ (fun u => obs.wave tau length (u,z.2)) z.1‖ ≤
      obs.cost length * delta ^ 2 / tau ∧
    ‖fderiv ℝ (fun u => fderiv ℝ (fderiv ℝ
      (fun x => obs.wave tau length (u,x))) z.2) z.1‖ ≤
      obs.cost length * delta ^ 2 / tau ^ 3 := by
  have hs := obs.wave_smooth tau length hW
  have hb := obs.weighted_jets tau length hbudget hell hell1 htau htaul hMg hCH hW
  have hv := actual_parameter_first_jet_le obs.domain_open hs (obs.sample_subset hz) 0
  simp only [norm_iteratedFDeriv_zero,Nat.zero_add] at hv
  refine ⟨hv.trans ?_, ?_⟩
  · apply (le_div_iff₀ htau).2
    simpa only [pow_one,mul_comm] using hb 1 (by omega) z hz
  · exact (actual_parameter_spatial_hessian_norm_le obs.domain_open hs
      (obs.sample_subset hz)).trans
      ((le_div_iff₀ (pow_pos htau 3)).2 (by simpa only [mul_comm] using hb 3 hj z hz))

end Native
end ActualSecondaryProbeObservation
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.ActualSecondaryProbeObservation.weighted_jets
#print axioms GlobalEmbedding.Continuation.ActualSecondaryProbeObservation.native_responses
