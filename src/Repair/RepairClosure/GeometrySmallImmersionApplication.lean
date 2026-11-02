import RepairClosure.GeometrySmallImmersion
import RepairClosure.InterfaceCanonicalApplication
import RepairClosure.InterfaceCanonicalApplicationError
import RepairClosure.InterfaceCanonicalApplicationFrequencies

/-!
# The original small exact immersion corollary, from actual initialization

The entrance is selected before K,T.  The initialization error then chooses
K,T large enough for that same entrance and for the requested image radius.
The repair output is actually used, and the final map is its inverse-scaled
slice. No general native-margin uniform repair theorem is assumed here:
the actual initialization proves its own quantitative coordinate margin.

The final theorem has only the original closed parallelizable source and
the given smooth positive metric as input. It permits disconnected and
empty sources. Auxiliary bundle geometry is manufactured from that given
metric internally, and is not an additional external assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Initialization
  Manifold IsManifold Set Function Bundle
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation.RepairClosure
open OriginalIntegration
universe uM

section SuccessorDimension
variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin (closedAmbientDimension (m+1)))
local notation "SI" => 𝓘(ℝ,Es)

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
/-- The literal repair construction and rescaling for one fixed
initialization. Taking the auxiliary parameter manifold to be the original
source avoids an extra zero-dimensional atlas construction. -/
theorem small_exact_immersion_from_initialization
    [IsContinuousRiemannianBundle Es (TangentSpace SI : M → Type _)]
    (data : InitializationData M m) (hm : 1 ≤ m)
    (metric0 : ContMDiffRiemannianMetric SI ∞ Es (TangentSpace SI : M → Type _))
    (r : ℝ) (hr : 0 < r) (p0 : M) :
    ∃ F : M → V,
      SmallExactImmersionConclusion (fun x => (metric0.inner x).toLinearMap₁₂) r F := by
  obtain ⟨B,mu,C,J,epsilon,t0,hCore,_hmu,_hC,_hJ,he,_ht,_h1,_hNative,hRepair⟩ :=
    canonical_initialization_uniform_coordinate_repair (P := M) (d := m+1)
      data hm metric0 data.charts 1 zero_lt_one
  let errorCost := canonicalMetricErrorNormFactor (m+1) (m+1) 440 * B.error 440
  have hErrorCost : 0 < errorCost :=
    mul_pos (canonicalMetricErrorNormFactor_pos _ _ _) (B.error_pos 440)
  let valueBound := B.value + geometrySmallImmersionValueFactor (closedAmbientDimension (m+1))
  obtain ⟨K,T,hK,hKT,hK0,hR0,hRadius,hError⟩ :=
    canonical_frequencies_enter B.K₀ B.R₀ errorCost epsilon (valueBound/r) hErrorCost he
  have hT : 0 < T := zero_lt_one.trans_le (hK.trans hKT)
  let g := canonicalOriginalGeometry data.charts data.charts T 1 (hK.trans hKT) le_rfl
  let F0 : M × M → V := fun px =>
    metricInitializationMap data.charts metric0 data.frame data.phase.selector K T hK px.2
  have hEntrance : RepairForEveryOriginalMetric g F0 1 epsilon t0 :=
    (hRepair K T 1 hK hKT le_rfl hK0 hR0).2.2
  have hErrorBound := core_original_joint_metric_error_bounds data.charts metric0 data.frame
    data.phase.selector B hCore K T hK hKT g.parameterChart g.Omega g.Q univ 440
  have hErrorSmall : paperAtlasCj 440
      (incrementsOriginalTensorCoordinates g.atlas g.parameterChart
        (fun p x => canonicalScaledMetric metric0 T x -
          inducedMetric (I := SI) (fun y => F0 (p,y)) x))
      g.differentiation g.samples < ENNReal.ofReal epsilon :=
    hErrorBound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff he).mpr hError)
  obtain ⟨Fstar,G,u,stage,out⟩ := hEntrance
    (fun _ x => canonicalScaledMetric metric0 T x)
    (fun _ x => canonicalScaledMetric_isSymm metric0 T x)
    (fun i => canonical_scaled_metric_coordinates_smooth data.charts metric0 data.frame
      T (hK.trans hKT) g.parameterChart i)
    (fun _ x v hv => canonicalScaledMetric_pos metric0 T hT x v hv)
    hErrorSmall
  have hSmall : B.value + geometrySmallImmersionValueFactor (closedAmbientDimension (m+1))*1
      < r*T := by
    have h := (div_lt_iff₀ hr).mp hRadius
    dsimp only [valueBound] at h
    nlinarith
  have hSmallOutput := geometry_small_immersion_of_repair g F0 Fstar
    (fun _ x => (metric0.inner x).toLinearMap₁₂)
    1 t0 B.value T r zero_lt_one hT hr G u stage out
    (fun z => hCore.map_value K T hK z.2) hSmall
  exact ⟨fun x => (T⁻¹ • Fstar) (p0,x), hSmallOutput.slice p0⟩

end SuccessorDimension

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
/-- Original `cor:small-immersion`: every closed parallelizable n-manifold,
n >= 2, with its given smooth positive metric has a smooth phase-regular
isometric immersion into R^(s_n+1) with arbitrarily small image.

No connectedness, nonemptiness, prepared atlas, quantitative phase margin,
repair supplier, or auxiliary-norm certificate is an external assumption. -/
theorem small_exact_immersion
    (hn : 2 ≤ n)
    (hpar : IsParallelizable (M := M) 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) n)
    (metric0 : ContMDiffRiemannianMetric 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) : M → Type _))
    (r : ℝ) (hr : 0 < r) :
    ∃ F : M → EuclideanSpace ℝ (Fin (closedAmbientDimension n)),
      SmallExactImmersionConclusion (fun x => (metric0.inner x).toLinearMap₁₂) r F := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hEmpty =>
    let : IsEmpty M := hEmpty
    exact ⟨fun _ => 0,small_exact_immersion_empty _ r hr⟩
  | inr hNonempty =>
    cases n with
    | zero => omega
    | succ m =>
      have hm : 1 ≤ m := by omega
      let : RiemannianBundle
          (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _) :=
        ⟨metric0.toRiemannianMetric⟩
      let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (m+1)))
          (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _) :=
        ⟨metric0.inner,metric0.contMDiff.continuous,fun _ _ _ => rfl⟩
      obtain ⟨data⟩ := exists_initializationData hm hpar
      exact small_exact_immersion_from_initialization data hm metric0 r hr
        (Classical.choice hNonempty)

/-- The constructed application satisfies the independent full source
statement, without importing a hypothetical native repair theorem. -/
theorem small_exact_immersion_complete : SmallExactImmersionStatement.{uM} := by
  exact @small_exact_immersion

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.small_exact_immersion_from_initialization
#print axioms GlobalEmbedding.Continuation.RepairClosure.small_exact_immersion
#print axioms GlobalEmbedding.Continuation.RepairClosure.small_exact_immersion_complete
