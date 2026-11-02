import OriginalIntegration.OriginalRepairTransport
import FaithfulCollars.OriginalFactoryReindex
import SourceCollarsBridge.PrimitiveUniformRepair

/-!
# Raw-free coordinate-margin repair on the original norm domains

All original coverings, raw functions, compact internal carriers, source
collars, smoothing packets, positive templates, finite increments, waits
and the one smooth limit are manufactured inside this theorem.  Its public
norms remain exactly Omega/Q.  The threshold is selected before all actual
atlases, reference maps, target metrics and observation orders.

The phase entrance in this module is explicitly the COORDINATE margin of
the actual true second form.  It is not silently identified with the
fixed auxiliary tangent-norm margin in defn:phase.  That separate original
norm conversion must be proved at a native entrance; this file alone is
not an assertion that the source's auxiliary-norm ambiguity is resolved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle Filter
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalIntegration
open SourceCollarsBridge FaithfulCollars
universe uM uP

section FixedManifolds
variable {b : OriginalRepairGeometryBudget} {m d N : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
private local instance originalCoordinateRepairChart : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance originalCoordinateRepairManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- Genuine finite reference bounds, with extended-norm inequalities so an
infinite original norm cannot pass through `toReal top = 0`. -/
structure OriginalCoordinateRepairReference
    (g : OriginalRepairGeometry b (m+1) d M P) (R : ℕ → ℝ)
    (lower margin : ℝ) (J : ℕ) (F0 : P × M → V) : Prop where
  smooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ F0
  map_bounds : ∀ j, j ≤ J → paperAtlasCj j
    (incrementsOriginalMapCoordinates g.atlas g.parameterChart F0)
    g.differentiation g.samples ≤ ENNReal.ofReal (R j)
  ellipticity : ∀ p i y, y ∈ g.Omega i → ∀ v : Es,
    lower*‖v‖^2 ≤ ‖fderiv ℝ (fun x => F0 (p,(g.atlas.chart i).symm x)) y v‖^2
  coordinate_phase : ∀ i z, parameterTensorModelEquiv (m+1) d z ∈ g.samples i →
    margin ≤ bestPhaseSupremum
      (repairReferenceFactoryField (g.seed F0)
        (fun p x => inducedMetric (I := 𝓘(ℝ,Es)) (fun y => F0 (p,y)) x) i z).1

def OriginalCoordinateRepairOpennessAt
    (b : OriginalRepairGeometryBudget) (R : ℕ → ℝ) (lower margin : ℝ)
    (J : ℕ) (rho epsilon t0 : ℝ) : Prop :=
  ∀ (g : OriginalRepairGeometry b (m+1) d M P) (F0 : P × M → V),
  OriginalCoordinateRepairReference g R lower margin J F0 →
  ∀ metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x),
  (∀ p x, (metric p x).IsSymm) →
  (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates g.atlas g.parameterChart metric i)
    (g.differentiation i)) →
  (∀ p x, ∀ v : TangentSpace 𝓘(ℝ,Es) x, v ≠ 0 → 0 < metric p x v v) →
  paperAtlasCj 440 (incrementsOriginalTensorCoordinates g.atlas g.parameterChart
    (fun p x => metric p x-inducedMetric (I := 𝓘(ℝ,Es)) (fun y => F0 (p,y)) x))
    g.differentiation g.samples < ENNReal.ofReal epsilon →
  ∃ (Fstar : P × M → V) (G u : ℕ → P × M → V) (stage : ℕ → ℕ),
    OriginalRepairConclusion g.atlas g.parameterChart g.Omega g.Q F0 metric rho t0 Fstar G u stage

end FixedManifolds

/-- Complete original-domain coordinate repair, with every analytic supply
constructed.  The universal atlas/count quantifiers are all after the
finite entrance constants.  The coordinate versus auxiliary margin is
kept explicit in the theorem name and input type. -/
theorem original_buffered_coordinate_repair
    {m d N : ℕ} (b : OriginalRepairGeometryBudget)
    (R : ℕ → ℝ) (hR : ∀ j, 0 ≤ R j) (lower margin : ℝ)
    (hLower : 0 < lower) (hMargin : 0 < margin)
    (hDim : 2 ≤ m+1) (hAmbient : (m+1)*(m+2)/2 < N)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ (J : ℕ) (epsilon t0 : ℝ),
      J = 197179 ∧ 442 ≤ J ∧ 0 < epsilon ∧ 0 < t0 ∧ t0 < 1 ∧
    ∀ (M : Type uM) (P : Type uP)
      [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [T2Space P] [CompactSpace P]
      [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
      [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
      [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)],
      OriginalCoordinateRepairOpennessAt (m := m) (d := d) (M := M) (P := P) (N := N)
        b R lower margin J rho epsilon t0 := by
  let smallRho := originalRepairInternalRadius (m+1) d b.parameterTransition b.spatialTransition rho
  have hSmall : 0 < smallRho := originalRepairInternalRadius_pos (m+1) d
    b.parameterTransition b.spatialTransition b.parameterTransition_nonneg rho hrho
  obtain ⟨J,epsilon,t0,hJ,h442,he,ht,h1,hOpen⟩ :=
    primitive_uniform_coordinate_openness.{uM,uP} (m := m) (d := d) (N := N)
      (b.primitive (m+1) d) R hR lower margin hLower hMargin hDim hAmbient smallRho hSmall
  refine ⟨J,epsilon,t0,hJ,h442,he,ht,h1,?_⟩
  intro M P topologyM topologyP hausdorffM hausdorffP compactP
    chartsM smoothM boundaryM chartsP smoothP auxiliaryNorm
  intro g F0 hRef metric hSym hMetricSmooth hPositive hError
  obtain ⟨c,hs,hp,hS,hP,hSupportS,hSupportP,hOmega,hQ,hBufferS,hBufferP,hGeom⟩ :=
    g.actual_compact_supply
  have hMap : ∀ j, j ≤ J →
      (paperAtlasCj j (incrementsOriginalMapCoordinates c.source c.parameter.chart F0)
        c.differentiation c.samples).toReal ≤ R j := by
    intro j hj
    have hle := (internal_map_norm_le_original g c hs hp hS hP hOmega hQ F0 j).trans
      (hRef.map_bounds j hj)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq (ENNReal.toReal_ofReal (hR j))
  have hEll : ∀ p i y, y ∈ c.Omega i → ∀ v : EuclideanSpace ℝ (Fin (m+1)),
      lower*‖v‖^2 ≤ ‖fderiv ℝ (fun x => F0 (p,(c.source.chart i).symm x)) y v‖^2 := by
    intro p i y hy v
    rw [hS i]
    exact hRef.ellipticity p (Fin.cast hs i) y (hOmega i hy) v
  have hPhase : ∀ i z, parameterTensorModelEquiv (m+1) d z ∈ c.samples i →
      margin ≤ bestPhaseSupremum
        (repairReferenceFactoryField (c.seed F0)
          (fun p x => inducedMetric (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
            (fun y => F0 (p,y)) x) i z).1 := by
    intro i z hz
    rw [compactSetup_factory_original c g.atlas g.Omega g.parameterChart g.Q hs hp hS hP]
    exact hRef.coordinate_phase (Fin.cast hs i.1,Fin.cast hp i.2) z
      (internalEvaluation_subset_original g.atlas c.source g.parameterChart c.parameter.chart
        hs hp hS hP g.Omega g.Q c.Omega c.Q univ hOmega hQ i hz)
  have hMetric := original_tensor_smooth_under_cast g c hs hp hS hP metric hMetricSmooth
  have hErr := (internal_tensor_norm_le_original g c hs hp hS hP hOmega hQ
    (fun p x => metric p x-inducedMetric (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
      (fun y => F0 (p,y)) x) 440).trans_lt hError
  obtain ⟨Fstar,G,u,stage,out⟩ := hOpen M P c hGeom F0 hRef.smooth hMap hEll hPhase
    metric hSym hMetric hPositive hErr
  have outOriginal := original_repair_conclusion_of_internal c
    (fun i => g.Omega (Fin.cast hs i)) (fun i => g.Q (Fin.cast hp i))
    b.parameterTransition b.spatialTransition b.parameterTransition_nonneg
    (original_parameter_transition_under_cast g c hs hp hS hP)
    (original_spatial_transition_under_cast g c hs hp hS hP)
    hRef.smooth hrho out
  exact ⟨Fstar,G,u,stage,original_repair_conclusion_reindex g c hs hp hS hP outOriginal⟩

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.original_buffered_coordinate_repair
