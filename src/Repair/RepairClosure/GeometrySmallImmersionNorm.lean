import OriginalIntegration.OriginalRepairGeometry

/-!
# Actual pointwise values from the unchanged original repair norm

The paper norm is a componentwise coordinate maximum.  The following
lemmas read its zero-th partial at a genuine original sample, then convert
the target Pi norm to the actual Euclidean target norm.  No connectedness,
nonemptiness, compact norm domain, or smoothness of the tested function is
needed for this zero-th order argument.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Bundle
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation.RepairClosure
open OriginalIntegration

/-- The fixed target-norm comparison, with a positive slack independent of
both chart counts and all actual maps. -/
def geometrySmallImmersionValueFactor (N : ℕ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ + 1

theorem geometrySmallImmersionValueFactor_pos (N : ℕ) :
    0 < geometrySmallImmersionValueFactor N := by
  unfold geometrySmallImmersionValueFactor
  positivity

/-- The zero-th coordinate partial belongs to every cumulative paper norm.
This proof does not assume any derivative exists. -/
theorem geometry_paperAtlasCj_value_le
    {ι : Type*} [Fintype ι] {n q : ℕ}
    (j : ℕ) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) (i : ι)
    (y : Fin n → ℝ) (hy : y ∈ S i) (c : Fin q) :
    ENNReal.ofReal ‖f i y c‖ ≤ paperAtlasCj j f O S := by
  unfold paperAtlasCj paperCoordinateCj
  exact le_iSup_of_le i (le_iSup_of_le ⟨[], by simp⟩
    (le_iSup_of_le ⟨y,hy⟩ (le_iSup_of_le c le_rfl)))

variable {b : OriginalRepairGeometryBudget} {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- Every physical point is reached by a sample of the original covering
and the original norm buffers. The returned point is not an internal
replacement sample. -/
theorem geometry_original_sample_at
    (g : OriginalRepairGeometry b n d M P) (p : P) (x : M) :
    ∃ (i : Fin g.atlas.count × Fin g.parameterCount) (y : Fin (n+d) → ℝ),
      y ∈ g.samples i ∧ incrementsOriginalJointPoint g.atlas g.parameterChart i y = (p,x) := by
  obtain ⟨s,hxs⟩ := g.atlas.cover x
  obtain ⟨a,hpa,hBall⟩ := g.parameterBuffer.cover p (mem_univ _)
  have hpQ : g.parameterChart a p ∈ g.Q a :=
    (hBall (Metric.mem_ball_self g.parameterBuffer.radius_pos)).1
  have hxSource := g.atlas.inner_subset s hxs
  have hxOmega := g.sourceBuffer.inner_original_norm s hxs
  let z : Ep × Es := (g.parameterChart a p,g.atlas.chart s x)
  let y := parameterTensorModelEquiv n d z
  have hsource := congrArg Prod.snd ((parameterTensorModelEquiv n d).symm_apply_apply z)
  have hparam := congrArg Prod.fst ((parameterTensorModelEquiv n d).symm_apply_apply z)
  change incrementsOriginalSourcePoint y = g.atlas.chart s x at hsource
  change incrementsOriginalParameterPoint y = g.parameterChart a p at hparam
  refine ⟨(s,a),y,?_,?_⟩
  · change (_ ∧ _) ∧ _ ∧ _ ∧ _
    rw [hsource,hparam]
    exact ⟨⟨(g.atlas.chart s).map_source hxSource,(g.parameterChart a).map_source hpa⟩,
      hxOmega,hpQ,mem_univ _⟩
  · unfold incrementsOriginalJointPoint
    rw [hsource,hparam,(g.atlas.chart s).left_inv hxSource,
      (g.parameterChart a).left_inv hpa]

/-- A strict original coordinate Cj bound gives an actual Euclidean value
bound on the same physical map. The only loss is a fixed target dimension
factor; no spatial or parameter chart count occurs. -/
theorem geometry_original_map_value_lt
    (g : OriginalRepairGeometry b n d M P)
    (F : P × M → EuclideanSpace ℝ (Fin N)) (j : ℕ)
    (rho : ℝ) (hrho : 0 < rho)
    (hNorm : paperAtlasCj j
      (incrementsOriginalMapCoordinates g.atlas g.parameterChart F)
      g.differentiation g.samples < ENNReal.ofReal rho) :
    ∀ p x, ‖F (p,x)‖ < geometrySmallImmersionValueFactor N * rho := by
  intro p x
  obtain ⟨i,y,hy,hpoint⟩ := geometry_original_sample_at g p x
  have hcomponent (c : Fin N) :
      ‖EuclideanSpace.equiv (Fin N) ℝ (F (p,x)) c‖ < rho := by
    have h := (geometry_paperAtlasCj_value_le j
      (incrementsOriginalMapCoordinates g.atlas g.parameterChart F)
      g.differentiation g.samples i y hy c).trans_lt hNorm
    change ENNReal.ofReal ‖EuclideanSpace.equiv (Fin N) ℝ
      (F (incrementsOriginalJointPoint g.atlas g.parameterChart i y)) c‖ <
      ENNReal.ofReal rho at h
    rw [hpoint] at h
    exact (ENNReal.ofReal_lt_ofReal_iff hrho).mp h
  have hpi : ‖EuclideanSpace.equiv (Fin N) ℝ (F (p,x))‖ ≤ rho :=
    (pi_norm_le_iff_of_nonneg hrho.le).mpr (fun c => (hcomponent c).le)
  calc
    ‖F (p,x)‖ = ‖(EuclideanSpace.equiv (Fin N) ℝ).symm
        (EuclideanSpace.equiv (Fin N) ℝ (F (p,x)))‖ := by rw [ContinuousLinearEquiv.symm_apply_apply]
    _ ≤ ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
        ‖EuclideanSpace.equiv (Fin N) ℝ (F (p,x))‖ :=
      (EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ * rho :=
      mul_le_mul_of_nonneg_left hpi (norm_nonneg _)
    _ < geometrySmallImmersionValueFactor N * rho := by
      unfold geometrySmallImmersionValueFactor
      nlinarith

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.geometry_original_sample_at
#print axioms GlobalEmbedding.Continuation.RepairClosure.geometry_original_map_value_lt
