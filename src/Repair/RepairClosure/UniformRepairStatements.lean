import OriginalIntegration.OriginalRepairGeometry

/-!
# Independent full repair statements and the precise numerical difference

These are proposition-valued definitions, with no axioms or proof holes.
The native statement records the manuscript's fixed auxiliary margin.
The coordinate statement records the proposed explicit chart-norm version.
They share every other input, quantifier and full original conclusion.

No completed repair theorem or solution module is imported here.  In
particular, the coordinate statement is not used to assert the native one.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation.RepairClosure
open OriginalIntegration
universe uM uP

section ActualData
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
private local instance repairContractProductChart : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance repairContractProductManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- The common finite reference inputs, written independently of either
repair implementation. -/
structure RepairReferenceCore
    (g : OriginalRepairGeometry b (m+1) d M P) (R : ℕ → ℝ)
    (lower : ℝ) (J : ℕ) (F0 : P × M → V) : Prop where
  smooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ F0
  map_bounds : ∀ j, j ≤ J → paperAtlasCj j
    (incrementsOriginalMapCoordinates g.atlas g.parameterChart F0)
    g.differentiation g.samples ≤ ENNReal.ofReal (R j)
  ellipticity : ∀ p i y, y ∈ g.Omega i → ∀ v : Es,
    lower * ‖v‖^2 ≤ ‖fderiv ℝ (fun x => F0 (p,(g.atlas.chart i).symm x)) y v‖^2

/-- The numerical native condition uses the unchanged original tangent
bundle instance and the same actual reference map. -/
def NativeReferencePhase
    (g : OriginalRepairGeometry b (m+1) d M P) (R : ℕ → ℝ)
    (lower mu : ℝ) (J : ℕ) (F0 : P × M → V)
    (core : RepairReferenceCore g R lower J F0) : Prop :=
  ∀ p x, mu ≤ truePhaseMargin (fun y => F0 (p,y))
    (parameterRound2_native_source_slice_contMDiff core.smooth p) x

/-- The coordinate numerical condition is explicitly a different
quantitative assumption; it is on the same actual second form. -/
def CoordinateReferencePhase
    (g : OriginalRepairGeometry b (m+1) d M P) (margin : ℝ) (F0 : P × M → V) : Prop :=
  ∀ i z, parameterTensorModelEquiv (m+1) d z ∈ g.samples i →
    margin ≤ bestPhaseSupremum
      (repairReferenceFactoryField (g.seed F0)
        (fun p x => inducedMetric (I := 𝓘(ℝ,Es)) (fun y => F0 (p,y)) x) i z).1

/-- The target and *all* output clauses are identical in both statements. -/
def RepairForEveryOriginalMetric
    (g : OriginalRepairGeometry b (m+1) d M P) (F0 : P × M → V)
    (rho epsilon t0 : ℝ) : Prop :=
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

end ActualData

/-- Full original numerical-native class.  This proposition is deliberately
not asserted as a theorem: its general uniform proof remains outstanding. -/
def UniformNativeRepairStatement : Prop :=
  ∀ {m d N : ℕ} (M : Type uM)
    [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (m+1)))
      (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
    (b : OriginalRepairGeometryBudget)
    (R : ℕ → ℝ) (_hR : ∀ j, 0 ≤ R j) (lower mu : ℝ)
    (_hLower : 0 < lower) (_hMu : 0 < mu)
    (_hDim : 2 ≤ m+1) (_hAmbient : (m+1)*(m+2)/2 < N)
    (rho : ℝ) (_hrho : 0 < rho),
  ∃ (J : ℕ) (epsilon t0 : ℝ), 442 ≤ J ∧ 0 < epsilon ∧ 0 < t0 ∧ t0 < 1 ∧
    ∀ (P : Type uP)
      [TopologicalSpace P] [T2Space P] [CompactSpace P]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
      (g : OriginalRepairGeometry b (m+1) d M P)
      (F0 : P × M → EuclideanSpace ℝ (Fin N))
      (core : RepairReferenceCore g R lower J F0),
      NativeReferencePhase g R lower mu J F0 core →
      RepairForEveryOriginalMetric g F0 rho epsilon t0

/-- The proposed explicit coordinate-margin class, with precisely the
same atlas, target, finite entrance and full conclusion quantifiers. -/
def UniformCoordinateRepairStatement : Prop :=
  ∀ {m d N : ℕ} (M : Type uM)
    [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (m+1)))
      (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
    (b : OriginalRepairGeometryBudget)
    (R : ℕ → ℝ) (_hR : ∀ j, 0 ≤ R j) (lower margin : ℝ)
    (_hLower : 0 < lower) (_hMargin : 0 < margin)
    (_hDim : 2 ≤ m+1) (_hAmbient : (m+1)*(m+2)/2 < N)
    (rho : ℝ) (_hrho : 0 < rho),
  ∃ (J : ℕ) (epsilon t0 : ℝ), 442 ≤ J ∧ 0 < epsilon ∧ 0 < t0 ∧ t0 < 1 ∧
    ∀ (P : Type uP)
      [TopologicalSpace P] [T2Space P] [CompactSpace P]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
      (g : OriginalRepairGeometry b (m+1) d M P)
      (F0 : P × M → EuclideanSpace ℝ (Fin N))
      (_core : RepairReferenceCore g R lower J F0),
      CoordinateReferencePhase g margin F0 →
      RepairForEveryOriginalMetric g F0 rho epsilon t0

end GlobalEmbedding.Continuation.RepairClosure
