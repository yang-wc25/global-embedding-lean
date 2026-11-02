import FaithfulCollars.LocalWorkingFamily
import FaithfulCollars.FixedBallRaw
import Smoothing.TensorLocalPrepared

/-!
# Actual local parameter raw supply

The parameter raw functions are the fixed smooth profile in each original
coordinate chart.  Their plateaus cover exactly the given geometric core
cover of K; global parameter compactness or a cover of all P is unnecessary.
Every raw field of the old `TensorLocalRawPreparation` is proved below.
Its own-jet profile is chosen before the finite index type, charts and K.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {ι E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace P] [T2Space P]

def originalLocalBallRaw (chart : ι → OpenPartialHomeomorph P E)
    (rho : ℝ) (i : ι) : P → ℝ :=
  scaledChartCutoff rho 1 (chart i)

def originalLocalBallEnlarged (chart : ι → OpenPartialHomeomorph P E)
    (rho : ℝ) (i : ι) : Set P :=
  (chart i).source ∩ (chart i) ⁻¹' closedBall 0 (rho / 4)

variable {chart : ι → OpenPartialHomeomorph P E} {K : Set P} {rho : ℝ}
  (g : OriginalLocalFixedBallGeometry chart K rho)

include g

theorem originalLocalBallRaw_compact_support (i : ι) :
    HasCompactSupport (originalLocalBallRaw chart rho i) ∧
    tsupport (originalLocalBallRaw chart rho i) ⊆
      (chart i).source ∩ (chart i) ⁻¹' closedBall 0 (3 * rho / 20) := by
  let e := chart i
  have ht : closedBall (0 : E) (3 * rho / 20) ⊆ e.target :=
    (closedBall_subset_closedBall (by linarith [g.radius_pos])).trans (g.target_buffer i)
  have hc : IsCompact (e.symm '' closedBall (0 : E) (3 * rho / 20)) :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono ht)
  have hs : Function.support (originalLocalBallRaw chart rho i) =
      e.source ∩ e ⁻¹' ball 0 (3 * rho / 20) := by
    simp only [originalLocalBallRaw, scaledChartCutoff, support_indicator,
      Function.support_comp_eq_preimage, scaledCutoffProfile_support rho 1 g.radius_pos le_rfl,
      mul_one, e]
  have hsub : Function.support (originalLocalBallRaw chart rho i) ⊆
      e.symm '' closedBall 0 (3 * rho / 20) := by
    intro p hp
    rw [hs] at hp
    exact ⟨e p, ball_subset_closedBall hp.2, e.left_inv hp.1⟩
  have hts : tsupport (originalLocalBallRaw chart rho i) ⊆
      e.symm '' closedBall 0 (3 * rho / 20) := closure_minimal hsub hc.isClosed
  refine ⟨hc.of_isClosed_subset (isClosed_tsupport _) hts, ?_⟩
  intro p hp
  obtain ⟨y, hy, rfl⟩ := hts hp
  refine ⟨e.map_target (ht hy), ?_⟩
  change e (e.symm y) ∈ closedBall 0 (3 * rho / 20)
  rw [e.right_inv (ht hy)]
  exact hy

theorem originalLocalBallRaw_working_inner (i : ι) :
    tsupport (originalLocalBallRaw chart rho i) ⊆
      (originalWorkingLocalFamily chart K rho g).inner i := by
  intro p hp
  have h := (originalLocalBallRaw_compact_support g i).2 hp
  exact ⟨h.1, closedBall_subset_ball (by linarith [g.radius_pos]) h.2⟩

theorem originalLocalBallRaw_enlarged (i : ι) :
    tsupport (originalLocalBallRaw chart rho i) ⊆ originalLocalBallEnlarged chart rho i := by
  intro p hp
  have h := (originalLocalBallRaw_compact_support g i).2 hp
  exact ⟨h.1, closedBall_subset_closedBall (by linarith [g.radius_pos]) h.2⟩

theorem originalLocalBallRaw_plateau_on (p : P) (hp : p ∈ K) :
    ∃ i, originalLocalBallRaw chart rho i p = 1 := by
  obtain ⟨i, hi⟩ := g.core_cover p hp
  refine ⟨i, scaledChartCutoff_one rho 1 g.radius_pos le_rfl (chart i) ?_⟩
  simpa only [mul_one] using ⟨hi.1, ball_subset_closedBall hi.2⟩

variable [ChartedSpace E P] [IsManifold 𝓘(ℝ, E) ∞ P]

theorem originalLocalBallRaw_smooth
    (hchart : ∀ i, chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ P) (i : ι) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (originalLocalBallRaw chart rho i) := by
  apply contMDiff_of_tsupport
  intro p hp
  have hps := ((originalLocalBallRaw_compact_support g i).2 hp).1
  have hs := (scaledCutoffProfile_contDiff (E := E) rho 1).contMDiff.contMDiffAt.comp p
    (contMDiffAt_of_mem_maximalAtlas (hchart i) hps)
  apply hs.congr_of_eventuallyEq
  filter_upwards [(chart i).open_source.mem_nhds hps] with y hy
  exact scaledChartCutoff_on_source rho 1 (chart i) hy

omit g in
/-- Actual finite raw production with constants before the chart count and
original parameter set.  No normalized partition or derivative estimate
for the desired normalized function is an input. -/
theorem exists_uniform_localWorkingRawPreparation
    (rho : ℝ) (hrho : 0 < rho) (T : ℕ → ℝ) (D : ℕ) :
    ∃ BP : ℕ → ℝ, (∀ j, 0 ≤ BP j) ∧
      ∀ (ι : Type*) [Fintype ι] (chart : ι → OpenPartialHomeomorph P E)
        (K : Set P) (g : OriginalLocalFixedBallGeometry chart K rho),
      (∀ i, chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ P) →
      (∀ i, tensorEnlargedSupportDegree (originalLocalBallEnlarged chart rho) i ≤ D) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (chart p).target,
        (chart p).symm y ∈ originalLocalBallEnlarged chart rho i →
        ‖iteratedFDeriv ℝ j (chart i ∘ (chart p).symm) y‖ ≤ T j) →
      ∃ R : TensorLocalRawPreparation (originalWorkingLocalFamily chart K rho g) K BP T D,
        R.raw = originalLocalBallRaw chart rho := by
  obtain ⟨BP, hBP, hjet⟩ := exists_scaledCutoffProfile_derivative_bounds (E := E) rho hrho
  refine ⟨BP, hBP, ?_⟩
  intro ι _ chart K g hchart hD htrans
  refine ⟨{
    raw := originalLocalBallRaw chart rho
    smooth := originalLocalBallRaw_smooth g hchart
    plateau_on := originalLocalBallRaw_plateau_on (chart := chart) g
    inner_support := originalLocalBallRaw_working_inner g
    enlarged := originalLocalBallEnlarged chart rho
    enlarged_support := originalLocalBallRaw_enlarged g
    degree := hD
    own_jets := ?_
    transition_jets := ?_ }, rfl⟩
  · intro i j y hy
    change ‖iteratedFDeriv ℝ j (originalLocalBallRaw chart rho i ∘ (chart i).symm) y‖ ≤ BP j
    rw [originalLocalBallRaw, iteratedFDeriv_scaledChartCutoff rho 1 (chart i) j hy]
    simpa only [one_pow, mul_one] using hjet 1 le_rfl j y
  · intro p i j hj y hy hx
    exact htrans p i j hj y hy (originalLocalBallRaw_enlarged g i hx)

end GlobalEmbedding.Continuation.FaithfulCollars
