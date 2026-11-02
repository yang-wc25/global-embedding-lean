import Upgrade.SupportedValueProbeResponse
import Upgrade.CompactValuePreparation

/-!
# The actual prepared value incidence has joint rank at least 2n+1

The same prepared unweighted legal value frame is used at every point of its
original neighborhood. Actual current normal projection error and the full
global probe tails are retained. The existing paired-value rank theorem adds
the true tangent rank, which follows from the exact induced metric.
-/

noncomputable section
open Bundle Manifold Set Module Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

local instance valueProbePairChartedSpace : ChartedSpace (E × E) (M × M) :=
  prodChartedSpace E M E M

/-- The original paired-value consumer applied to one actual prepared packet
of the full probe family. The displayed numerical inputs are discharged from
the original C² estimate and remainder convergence in the scale endpoint. -/
theorem ValuePreparedNeighborhood.actual_probe_joint_rank
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
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius) (z : M × M) (hz : z ∈ p.neighborhood)
    (hprojection : ∀ l,
      ‖(normalSpace (I := IM) (probe.map t u) z.1).starProjection ((packet.waves l).value x) -
        (packet.waves l).value x‖ ≤ p.tolerance)
    (hbudget : ∀ l, probe.weight (labels l) ^ 2 * (probe.etaV t + probe.constant * ‖u‖) ≤
      p.tolerance / 2) :
    2 * n + 1 ≤ finrank ℝ (LinearMap.range
      (mfderiv ((𝓘(ℝ, Fin (finrank ℝ (ProbeParameters r)) → ℝ)).prod 𝓘(ℝ, E × E))
        𝓘(ℝ, Fin N → ℝ) (euclideanCoincidenceMap (probe.toProbeGeometry.coordinateMap t))
          (probeParameterCoordinates r u, z)).toLinearMap) := by
  let g := probe.toProbeGeometry
  let α := probeParameterCoordinates r
  let G := g.coordinateMap t
  let v := fun l ↦ (packet.waves l).value x
  let a := t ^ ((56 : ℝ) / 5)
  let θ := fun l ↦ probe.weight (labels l) * (waves (labels l)).phase z.1 / t ^ ((6 : ℝ) / 5)
  let d := fun (b : Bool) l ↦ α (-(probe.weight (labels l) ^ 2) • Pi.single (labels l,b) 1)
  let ex := fun (b : Bool) l ↦ fderiv ℝ (fun q ↦ G q z.1) (α u) (d b l) -
    (a * probeTrig b (θ l)) • v l
  let ey := fun (b : Bool) l ↦ fderiv ℝ (fun q ↦ G q z.2) (α u) (d b l)
  have hrawx (b : Bool) (l : Fin (n + 1)) : ‖ex b l‖ ≤ a * p.tolerance := by
    have hvar : ‖(waves (labels l)).value z.1 - v l‖ ≤ p.tolerance / 4 := by
      rw [hlabels l]
      exact (p.value_variation z hz l).le
    have hr := probe.value_unweighted_response_reference t ht htt u hu (labels l) b z.1
      (v l) (p.tolerance / 4) hvar
    have hD := g.coordinateMap_parameter_response t ht htt u
      (-(probe.weight (labels l) ^ 2) • Pi.single (labels l,b) 1) hu z.1
    have he : ‖ex b l‖ ≤ a *
        (probe.weight (labels l) ^ 2 * (probe.etaV t + probe.constant * ‖u‖) + p.tolerance / 4) := by
      dsimp only [ex, G, d]
      rw [hD]
      exact hr
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
    have hb := hbudget l
    linarith [p.tolerance_pos]
  have hrawy (b : Bool) (l : Fin (n + 1)) : ‖ey b l‖ ≤ a * p.tolerance := by
    have haway : (waves (labels l)).cutoff z.2 = 0 := by
      rw [hlabels l]
      exact (p.cutoff z hz l).2
    have hr := probe.value_unweighted_response_away t ht htt u hu (labels l) b z.2 haway
    have hD := g.coordinateMap_parameter_response t ht htt u
      (-(probe.weight (labels l) ^ 2) • Pi.single (labels l,b) 1) hu z.2
    dsimp only [ey, G, d]
    rw [hD]
    exact hr.trans (mul_le_mul_of_nonneg_left
      ((hbudget l).trans (half_le_self p.tolerance_pos.le)) (Real.rpow_nonneg ht.le _))
  have hdomain : α u ∈ g.coordinateDomain := by
    change α.symm (α u) ∈ Metric.ball 0 g.radius
    simpa only [ContinuousLinearEquiv.symm_apply_apply, Metric.mem_ball, dist_zero_right] using hu
  have hnewimm : Injective (mfderiv IM 𝓘(ℝ, V) (G (α u)) z.1) := by
    change Injective (mfderiv IM 𝓘(ℝ, V) (probe.map t (α.symm (α u))) z.1)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact immersion_of_inducedMetric_eq F₀ (probe.map t u) z.1
      (probe.metric t ht htt u hu z.1) (himm z.1)
  have hproj (l : Fin (n + 1)) :
      ‖(normalSpace (I := IM) (G (α u)) z.1).starProjection (v l) - v l‖ ≤ p.tolerance := by
    change ‖(normalSpace (I := IM) (probe.map t (α.symm (α u))) z.1).starProjection
      (v l) - v l‖ ≤ p.tolerance
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hprojection l
  have hrank := coincidence_joint_rank_of_paired_value_responses
    G g.coordinateDomain g.coordinateDomain_open (g.coordinateMap_joint_smooth t ht htt)
    (α u) hdomain z.1 z.2 hnewimm
    (a := a) (m := p.margin) (eta := p.tolerance) (eps := p.tolerance)
    (Real.rpow_pos_of_pos ht _) p.tolerance_pos.le p.tolerance_pos.le
    θ (d false) (d true) v (ex false) (ey false) (ex true) (ey true)
    p.frame_lower
    (fun l ↦ by dsimp only [ex, probeTrig]; simp only [Bool.false_eq_true, ite_false]; abel)
    (fun _ ↦ rfl)
    (fun l ↦ by dsimp only [ex, probeTrig]; simp only [ite_true]; abel)
    (fun _ ↦ rfl) hproj (hrawx false) (hrawy false) (hrawx true) (hrawy true)
    (by simpa only [Nat.cast_add, Nat.cast_one] using p.rank_budget)
  have hnum : n + (n + 1) = 2 * n + 1 := by omega
  simpa only [finrank_euclideanSpace, Fintype.card_fin, hnum] using hrank

#print axioms ValuePreparedNeighborhood.actual_probe_joint_rank

end GlobalEmbedding.Upgrade
