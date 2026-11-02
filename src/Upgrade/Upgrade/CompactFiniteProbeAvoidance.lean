import Upgrade.CompactProbeScales
import Upgrade.SupportedPreparedAvoidance

/-!
# Finite assembly of actual probe bad parameters

This is the common finite-union and scale-selection step used only AFTER the
actual rank or supported/value geometry has supplied its prepared-region null
theorems and the original-C² no-new-incidence theorem. No incidence rank or
global good parameter is a hypothesis. The original probe array, norm, map,
positive ball, and original-C² estimate are retained.
-/

noncomputable section
open Set Filter Bundle Manifold MeasureTheory GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem exists_probe_parameter_avoiding_finite_regions
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F hF}
    (probe : ExactProbeFamily F hF A waves)
    {X ι : Type*} [Fintype ι] (K : Set X) (regions : ι → Set X)
    (bad : ℝ → ProbeParameters r → X → Prop)
    (enoNew : ℝ) (henoNew : 0 < enoNew)
    (hnoNew : ∀ t, 0 < t → t < probe.threshold → ∀ u, ‖u‖ < probe.radius →
      probeAtlasCj A 2 (probe.map t u - F) ≤ ENNReal.ofReal enoNew →
      ∀ x ∈ K, bad t u x → ∃ i, x ∈ regions i)
    (hlocal : ∀ i, ∃ rho > 0, rho ≤ probe.radius ∧ ∃ t0 > 0, t0 ≤ probe.threshold ∧
      ∀ t, 0 < t → t < t0 → volume (probeParameterCoordinates r ''
        {u : ProbeParameters r | ‖u‖ < rho ∧ ∃ x ∈ regions i, bad t u x}) = 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ t : ℝ, 0 < t ∧ t < probe.threshold ∧ ∃ u : ProbeParameters r,
      ‖u‖ < probe.radius ∧
      probeAtlasCj A 2 (probe.map t u - F) ≤ ENNReal.ofReal epsilon ∧
      (∀ x, inducedMetric (I := IM) (probe.map t u) x = inducedMetric (I := IM) F x) ∧
      ∀ x ∈ K, ¬ bad t u x := by
  classical
  choose localRadius hlocalRadius hlocalRadiusBound localScale hlocalScale hlocalScaleBound hlocalNull using hlocal
  obtain ⟨radius, hradius, hradiusle⟩ := finite_positive_common_lower_bound localRadius hlocalRadius
  obtain ⟨scale, hscale, hscalele⟩ := finite_positive_common_lower_bound localScale hlocalScale
  let rho := min radius probe.radius
  have hrho : 0 < rho := lt_min hradius probe.radius_pos
  have hrhoprobe : rho ≤ probe.radius := min_le_right _ _
  have hrholocal (i : ι) : rho ≤ localRadius i := (min_le_left _ _).trans (hradiusle i)
  obtain ⟨closeScale, hcloseScale, hcloseThreshold, hclose⟩ :=
    probe.eventually_originalC2_small (lt_min hepsilon henoNew)
  let t := min scale closeScale / 2
  have ht : 0 < t := half_pos (lt_min hscale hcloseScale)
  have htScale : t < scale := (half_lt_self (lt_min hscale hcloseScale)).trans_le (min_le_left _ _)
  have htClose : t < closeScale := (half_lt_self (lt_min hscale hcloseScale)).trans_le (min_le_right _ _)
  have htt : t < probe.threshold := htClose.trans_le hcloseThreshold
  let Bad : Set (ProbeParameters r) := {u | ‖u‖ < rho ∧ ∃ x ∈ K, bad t u x}
  let LocalBad : ι → Set (ProbeParameters r) := fun i ↦
    {u | ‖u‖ < localRadius i ∧ ∃ x ∈ regions i, bad t u x}
  have hnull (i : ι) : volume (probeParameterCoordinates r '' LocalBad i) = 0 :=
    hlocalNull i t ht (htScale.trans_le (hscalele i))
  have hsub : probeParameterCoordinates r '' Bad ⊆
      ⋃ i : ι, probeParameterCoordinates r '' LocalBad i := by
    rintro v ⟨u, hu, rfl⟩
    obtain ⟨x, hx, hbad⟩ := hu.2
    have huProbe : ‖u‖ < probe.radius := hu.1.trans_le hrhoprobe
    have hc2 := hclose t ht htClose u huProbe
    obtain ⟨i, hxi⟩ := hnoNew t ht htt u huProbe
      (hc2.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))) x hx hbad
    exact mem_iUnion.mpr ⟨i, u, ⟨hu.1.trans_le (hrholocal i), x, hxi, hbad⟩, rfl⟩
  have hBadNull : volume (probeParameterCoordinates r '' Bad) = 0 :=
    measure_mono_null hsub (measure_iUnion_null hnull)
  obtain ⟨u, hu, hnot⟩ := exists_small_probe_parameter_outside_null Bad rho hrho hBadNull
  have huProbe : ‖u‖ < probe.radius := hu.trans_le hrhoprobe
  refine ⟨t, ht, htt, u, huProbe,
    (hclose t ht htClose u huProbe).trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)),
    probe.metric t ht htt u huProbe, ?_⟩
  intro x hx hbad
  exact hnot ⟨hu, x, hx, hbad⟩

end GlobalEmbedding.Upgrade
