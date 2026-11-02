import Upgrade.SupportedValueProbeRank

/-!
# Actual null exceptional parameters on one prepared value neighborhood

This invokes the accepted finite-parameter avoidance theorem for the literal
value difference of the coordinate-transported original probe family. Its
rank is derived from the actual paired responses and exact metric. The fixed
finite atlas itself supplies second countability, including an empty atlas.
-/

noncomputable section
open Bundle Manifold Set Module Function MeasureTheory
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline

/-- The existing finite topological chart cover already gives second
countability. This adds no manifold, connectedness or nonempty hypothesis. -/
theorem bufferedAtlas_secondCountable
    {M E : Type*} [TopologicalSpace M] [PseudoMetricSpace E] [SecondCountableTopology E]
    (A : BufferedAtlas M E) : SecondCountableTopology M := by
  letI : ∀ i : Fin A.count, SecondCountableTopology (A.chart i).source :=
    fun i ↦ (A.chart i).secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (fun i ↦ (A.chart i).open_source)
  apply eq_univ_iff_forall.mpr
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  exact mem_iUnion.mpr ⟨i, A.inner_subset i hi⟩

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

local instance valueProbeAvoidancePairChartedSpace : ChartedSpace (E × E) (M × M) :=
  prodChartedSpace E M E M

/-- For the actual full probe family, the original coincidence bad parameters
on the SAME prepared pair neighborhood form a null set in the fixed parameter
coordinates. All four global value tails and the actual new normal projector
are used to derive the required joint rank. -/
theorem ValuePreparedNeighborhood.exact_probe_value_bad_parameters_null
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    {packet : LegalValueWavePacket F₀ hF₀ x y (n + 1)} {i : Fin A.count}
    {hx : x ∈ interior (A.support i)}
    (p : ValuePreparedNeighborhood A hA packet i hx)
    (himm : ∀ z, Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (r : ℕ) (waves : Fin r → LocalLegalWave F₀ hF₀)
    (labels : Fin (n + 1) → Fin r) (hlabels : ∀ j, waves (labels j) = packet.waves j)
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (ρ : ℝ) (hρradius : ρ ≤ probe.radius)
    (hbudget : ∀ l, probe.weight (labels l) ^ 2 * (probe.etaV t + probe.constant * ρ) ≤
      p.tolerance / 2)
    (hprojection : ∀ u : ProbeParameters r, ‖u‖ < ρ → ∀ z ∈ p.neighborhood, ∀ l,
      ‖(normalSpace (I := IM) (probe.map t u) z.1).starProjection ((packet.waves l).value x) -
        (packet.waves l).value x‖ ≤ p.tolerance) :
    volume (probeParameterCoordinates r '' {u : ProbeParameters r | ‖u‖ < ρ ∧
      ∃ z ∈ p.neighborhood, probe.map t u z.1 = probe.map t u z.2}) = 0 := by
  letI : SecondCountableTopology M := bufferedAtlas_secondCountable A
  letI : IsManifold 𝓘(ℝ, E × E) ∞ (M × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := IM) (I' := IM) (n := ∞) M M
  let g := probe.toProbeGeometry
  let α := probeParameterCoordinates r
  let G := g.coordinateMap t
  let R : Set ((Fin (finrank ℝ (ProbeParameters r)) → ℝ) × (M × M)) :=
    {w | ‖α.symm w.1‖ < ρ ∧ w.2 ∈ p.neighborhood ∧ G w.1 w.2.1 = G w.1 w.2.2}
  have hRelevant : ∀ w ∈ R, w.1 ∈ g.coordinateDomain ∧ euclideanCoincidenceMap G w = 0 := by
    intro w hw
    refine ⟨?_, (euclideanCoincidenceMap_eq_zero_iff G w).mpr hw.2.2⟩
    change α.symm w.1 ∈ Metric.ball 0 probe.radius
    simpa only [Metric.mem_ball, dist_zero_right] using hw.1.trans_le hρradius
  have hnull : volume (Prod.fst '' R) = 0 := by
    apply finite_parameter_avoidance (a := 2 * n) («E» := E × E)
      (by simp [Module.finrank_prod, two_mul]) g.coordinateDomain g.coordinateDomain_open
      (euclideanCoincidenceMap G)
      (contMDiffOn_euclideanCoincidenceMap G g.coordinateDomain (g.coordinateMap_joint_smooth t ht htt))
      R hRelevant
      (k := 2 * n + 1) (by omega)
    intro w hw
    have hu : ‖α.symm w.1‖ < probe.radius := hw.1.trans_le hρradius
    have hbudget' (l : Fin (n + 1)) :
        probe.weight (labels l) ^ 2 * (probe.etaV t + probe.constant * ‖α.symm w.1‖) ≤
          p.tolerance / 2 := by
      apply (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hw.1.le probe.constant_nonneg)) (sq_nonneg _)).trans
      exact hbudget l
    have hr := p.actual_probe_joint_rank himm r waves labels hlabels probe t ht htt
      (α.symm w.1) hu w.2 hw.2.1 (hprojection _ hw.1 _ hw.2.1) hbudget'
    change 2 * n + 1 ≤ finrank ℝ (LinearMap.range
      (mfderiv ((𝓘(ℝ, Fin (finrank ℝ (ProbeParameters r)) → ℝ)).prod 𝓘(ℝ, E × E))
        𝓘(ℝ, Fin N → ℝ) (euclideanCoincidenceMap G)
          (α (α.symm w.1), w.2)).toLinearMap) at hr
    rw [ContinuousLinearEquiv.apply_symm_apply] at hr
    exact hr
  apply measure_mono_null ?_ hnull
  rintro v ⟨u, hu, rfl⟩
  obtain ⟨z, hz, hcoin⟩ := hu.2
  refine ⟨(α u, z), ⟨?_, hz, ?_⟩, rfl⟩
  · simpa only [ContinuousLinearEquiv.symm_apply_apply] using hu.1
  · change probe.map t (α.symm (α u)) z.1 = probe.map t (α.symm (α u)) z.2
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hcoin

#print axioms bufferedAtlas_secondCountable
#print axioms ValuePreparedNeighborhood.exact_probe_value_bad_parameters_null

end GlobalEmbedding.Upgrade
