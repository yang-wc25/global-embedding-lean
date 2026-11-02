import SourceCollarsBridge.LiftedSetup
import Repair.ClosureNovUniformRepair

/-!
# The existing coordinate repair endpoint with primitive geometry budgets

This is the old coordinate repair conclusion for the literal old Setup,
now reached through `PrimitiveGeometryBounds`.  The class is constructed
before the manifolds, atlas counts, reference map, metric and every
observation order.  Its actual source collars and parent estimates are
produced internally; no comparison of generated profiles is an entrance
assumption.

This theorem retains the old Setup's compact norm-domain and raw-family
inputs.  It does not identify that candidate entrance with the entire
original paper entrance.  The independent target review must still check
those inputs and the intrinsic auxiliary-norm conversion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle Filter
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation.SourceCollarsBridge
universe uM uP

section FixedManifolds
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private local instance primitiveRepairProductChart : ChartedSpace X (P × M) :=
  prodChartedSpace Ep P D M
private local instance primitiveRepairProductManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

/-- Only the old geometry's proof budgets changed, so every field of its
actual repair conclusion transfers to the unchanged original Setup. -/
theorem full_original_conclusion_of_lifted
    {b : PrimitiveGeometryBudget} {g : SourceCollarNovSetup (m+1) d M P}
    (hg : PrimitiveGeometryBounds b g)
    {F0 Fstar : P × M → V}
    {metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x)}
    {rho t0 : ℝ} {G u : ℕ → P × M → V} {stage : ℕ → ℕ}
    (out : ClosureNovFullOriginalConclusion hg.liftedSetup F0 metric rho t0 Fstar G u stage) :
    ClosureNovFullOriginalConclusion g F0 metric rho t0 Fstar G u stage := by
  cases out
  constructor <;> assumption

/-- The original full conclusion of the existing repair consumer, with
only original primitive geometry comparisons at the public entrance. -/
def PrimitiveOriginalOpennessAt
    (b : PrimitiveGeometryBudget) (c : RepairOriginalNumericalSetup m d N)
    (Jstar : ℕ) (rho epsilon t0 : ℝ) : Prop :=
    ∀ (g : SourceCollarNovSetup (m+1) d M P)
      (_hg : PrimitiveGeometryBounds b g) (F0 : P × M → V)
      (_hSmooth : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ F0)
      (_hMap : ∀ j, j ≤ Jstar →
        (paperAtlasCj j (incrementsOriginalMapCoordinates g.source g.parameter.chart F0)
          g.differentiation g.samples).toReal ≤ c.mapBounds j)
      (_hEll : ∀ p i y, y ∈ g.Omega i → ∀ v : D,
        c.lower*‖v‖^2 ≤ ‖fderiv ℝ (fun x => F0 (p,(g.source.chart i).symm x)) y v‖^2)
      (_hPhase : ∀ i z, parameterTensorModelEquiv (m+1) d z ∈ g.samples i →
        c.referenceBudget.phaseMargin ≤ bestPhaseSupremum
          (repairReferenceFactoryField (g.seed F0)
            (fun p x => inducedMetric (I := 𝓘(ℝ,D)) (fun y => F0 (p,y)) x) i z).1)
      (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
      (_hSym : ∀ p x, (metric p x).IsSymm)
      (_hMetricSmooth : ∀ i, ContDiffOn ℝ ∞
        (incrementsOriginalTensorCoordinates g.source g.parameter.chart metric i) (g.differentiation i))
      (_hPositive : ∀ p x, ∀ v : TangentSpace 𝓘(ℝ,D) x, v ≠ 0 → 0 < metric p x v v),
    paperAtlasCj 440 (incrementsOriginalTensorCoordinates g.source g.parameter.chart
      (fun p x => metric p x-inducedMetric (I := 𝓘(ℝ,D)) (fun y => F0 (p,y)) x))
      g.differentiation g.samples < ENNReal.ofReal epsilon →
    ∃ (Fstar : P × M → V) (G u : ℕ → P × M → V) (stage : ℕ → ℕ),
      ClosureNovFullOriginalConclusion g F0 metric rho t0 Fstar G u stage

end FixedManifolds

/-- Fixed primitive numerical data suffice for the old uniform coordinate
repair endpoint.  Both the numerical class and its finite entrance are
chosen before every atlas count and before the particular reference map. -/
theorem primitive_uniform_coordinate_openness
    {m d N : ℕ} (b : PrimitiveGeometryBudget)
    (R : ℕ → ℝ) (hR : ∀ j, 0 ≤ R j) (lower margin : ℝ)
    (hLower : 0 < lower) (hMargin : 0 < margin)
    (hDim : 2 ≤ m+1) (hAmbient : (m+1)*(m+2)/2 < N)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ (Jstar : ℕ) (epsilon t0 : ℝ),
      Jstar = 197179 ∧ 442 ≤ Jstar ∧ 0 < epsilon ∧ 0 < t0 ∧ t0 < 1 ∧
    ∀ (M : Type uM) (P : Type uP)
      [TopologicalSpace M] [TopologicalSpace P]
      [T2Space M] [T2Space P] [CompactSpace P]
      [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
      [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
      [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)],
      PrimitiveOriginalOpennessAt (m := m) (d := d) (N := N) (M := M) (P := P) b
        (b.numericalSetup (d := d) R hR lower margin hLower hMargin hDim hAmbient)
        Jstar rho epsilon t0 := by
  obtain ⟨Jstar,epsilon,t0,hJstar,h442,hepsilon,ht0,ht01,hOpen⟩ :=
    closureNov_original_coordinate_uniform_smooth_openness
      (b.numericalSetup (d := d) R hR lower margin hLower hMargin hDim hAmbient) rho hrho
  refine ⟨Jstar,epsilon,t0,hJstar,h442,hepsilon,ht0,ht01,?_⟩
  intro M P topologyM topologyP hausdorffM hausdorffP compactP
    chartsM smoothM boundaryM chartsP smoothP auxiliaryNorm
  intro g hg F0 hSmooth hMap hEll hPhase metric hSym hMetricSmooth hPositive hError
  obtain ⟨Fstar,G,u,stage,out⟩ := hOpen M P hg.liftedSetup
    (hg.geometryBounds R hR lower margin hLower hMargin hDim hAmbient)
    F0 hSmooth hMap hEll hPhase metric hSym hMetricSmooth hPositive hError
  exact ⟨Fstar,G,u,stage,full_original_conclusion_of_lifted hg out⟩

end GlobalEmbedding.Continuation.SourceCollarsBridge

#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.full_original_conclusion_of_lifted
#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.primitive_uniform_coordinate_openness
