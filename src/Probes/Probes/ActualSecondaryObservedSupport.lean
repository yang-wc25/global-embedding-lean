import Probes.ActualSecondaryObservedPhysicalIdentity
import Probes.ActualSecondaryObservationSum
import Smoothing.ParameterRound2GlobalCorrectionSupport

/-!
# True inactive germs of the observed physical secondary residual

The zero germ is derived from the original supported constructed wave and
from its forcing support. It is not inferred merely from a cutoff value
being zero, and it does not assume continuity of a totalized inverse chart
outside the actual observation domain.
-/

noncomputable section
open Manifold Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
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

theorem actual_joint_metric_linearization_zero_germ
    (F U : X → V) (z : X) (hU : U =ᶠ[𝓝 z] fun _ => 0) :
    actualJointMetricLinearization F U =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [hU.eventuallyEq_nhds] with y hy
  have hs : (fun x : D => U (y.1,x)) =ᶠ[𝓝 y.2] fun _ => 0 :=
    hy.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  exact actual_coordinate_metric_linearization_zero_germ
    (fun x => F (y.1,x)) (fun x => U (y.1,x)) y.2 hs

theorem actual_observed_secondary_forcing_zero_off_support
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (d : ActualSecondaryPieceData (I := 𝓙) (m := m) F hF n j ell Mg CH delta W)
    (kappa : X → Ep × M) (tau : ℝ) (z : X) (hz : kappa z ∉ d.support) :
    actualObservedSecondaryForcingTensor F hF d kappa tau z = 0 := by
  unfold actualObservedSecondaryForcingTensor
  split_ifs with hsource
  · have hR : d.hR (d.chart (kappa z)) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hh := d.forcing_support (d.chart (kappa z)) (d.chart.map_source hsource) (Or.inl hmem)
      rw [d.chart.left_inv hsource] at hh
      exact hz hh
    have hI : d.hI (d.chart (kappa z)) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hh := d.forcing_support (d.chart (kappa z)) (d.chart.map_source hsource) (Or.inr hmem)
      rw [d.chart.left_inv hsource] at hh
      exact hz hh
    have hcoeff : (fun i a =>
        Complex.exp ((((d.chart (kappa z)).2 0 / tau : ℝ) : ℂ) * Complex.I) *
          ((d.hR (d.chart (kappa z)) i a : ℂ) + Complex.I * (d.hI (d.chart (kappa z)) i a : ℂ))) =
        (0 : Fin (m+1) → Fin (m+1) → ℂ) := by
      funext i a
      simp only [hR, hI, Pi.zero_apply, Complex.ofReal_zero, mul_zero, add_zero]
    unfold actualSecondaryLocalForcingTensor
    rw [hcoeff, map_zero]
    ext v w
    rfl
  · rfl

theorem actual_observed_secondary_error_zero_germ
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (d : ActualSecondaryPieceData (I := 𝓙) (m := m) F hF n j ell Mg CH delta W)
    (kappa : X → Ep × M) (tau : ℝ) (length : ℕ)
    (hW : IsOpen W) (z : X) (hkappa : ContinuousAt kappa z)
    (hzW : kappa z ∈ W) (hz : kappa z ∉ d.support) :
    actualObservedSecondaryPhysicalError F hF d kappa tau length =ᶠ[𝓝 z] fun _ => 0 := by
  have hw := parameterRound2_relative_observation_zero_germ (d.wave tau length) W d.support hW
    (d.wave_regular tau length hW).2 kappa z hkappa hzW hz
  have hl := actual_joint_metric_linearization_zero_germ
    (fun y => F (kappa y).1 (kappa y).2) (d.wave tau length ∘ kappa) z hw
  have hopen : IsOpen (Subtype.val '' (Subtype.val ⁻¹' d.support : Set W)ᶜ) :=
    hW.isOpenMap_subtype_val _ d.support_closed.isOpen_compl
  have hmem : kappa z ∈ Subtype.val '' (Subtype.val ⁻¹' d.support : Set W)ᶜ :=
    ⟨⟨kappa z,hzW⟩,hz,rfl⟩
  have hn : ∀ᶠ y in 𝓝 z, kappa y ∉ d.support := by
    filter_upwards [hkappa.eventually (hopen.mem_nhds hmem)] with y hy
    obtain ⟨v,hv,he⟩ := hy
    change v.val ∉ d.support at hv
    simpa only [he] using hv
  filter_upwards [hl, hn] with y hlin hnot
  change actualJointMetricLinearization (fun y => F (kappa y).1 (kappa y).2)
    (d.wave tau length ∘ kappa) y - actualObservedSecondaryForcingTensor F hF d kappa tau y = 0
  rw [hlin, actual_observed_secondary_forcing_zero_off_support F hF n j ell Mg CH delta W d kappa tau y hnot]
  exact sub_self (0 : D →L[ℝ] D →L[ℝ] ℝ)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_observed_secondary_forcing_zero_off_support
#print axioms GlobalEmbedding.Continuation.actual_observed_secondary_error_zero_germ
