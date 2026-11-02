import Repair.ClosureNovClassConclusion

/-! The actual weighted datum, including all native phase and positive
reserve certificates, selected from the proved original-map producer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle Filter
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation
universe uM uP
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
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
private local instance : ChartedSpace X (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

/-- The full original repair assertion at a prescribed finite entrance.
All chart and map quantifiers are displayed here; the conclusion contains
only the original source/parameter norms and the actual common sequence. -/
def ClosureNovOriginalOpennessAt (c : RepairOriginalNumericalSetup m d N)
    (Jstar : ℕ) (rho epsilon t0 : ℝ) : Prop :=
    ∀ (g : SourceCollarNovSetup (m+1) d M P)
      (hg : SourceCollarNovGeometryBounds c g) (F0 : P × M → V)
      (hSmooth : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ F0)
      (hMap : ∀ j, j ≤ Jstar →
        (paperAtlasCj j (incrementsOriginalMapCoordinates g.source g.parameter.chart F0)
          g.differentiation g.samples).toReal ≤ c.mapBounds j)
      (hEll : ∀ p i y, y ∈ g.Omega i → ∀ v : D,
        c.lower*‖v‖^2 ≤ ‖fderiv ℝ (fun x => F0 (p,(g.source.chart i).symm x)) y v‖^2)
      (hPhase : ∀ i z, parameterTensorModelEquiv (m+1) d z ∈ g.samples i →
        c.referenceBudget.phaseMargin ≤ bestPhaseSupremum
          (repairReferenceFactoryField (g.seed F0)
            (fun p x => inducedMetric (I := 𝓘(ℝ,D)) (fun y => F0 (p,y)) x) i z).1)
      (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hMetricSmooth : ∀ i, ContDiffOn ℝ ∞
        (incrementsOriginalTensorCoordinates g.source g.parameter.chart metric i) (g.differentiation i))
      (hPositive : ∀ p x, ∀ v : TangentSpace 𝓘(ℝ,D) x, v ≠ 0 → 0 < metric p x v v),
    paperAtlasCj 440 (incrementsOriginalTensorCoordinates g.source g.parameter.chart
      (fun p x => metric p x-inducedMetric (I := 𝓘(ℝ,D)) (fun y => F0 (p,y)) x))
      g.differentiation g.samples < ENNReal.ofReal epsilon →
    ∃ (Fstar : P × M → V) (G u : ℕ → P × M → V) (stage : ℕ → ℕ),
      ClosureNovFullOriginalConclusion g F0 metric rho t0 Fstar G u stage

end GlobalEmbedding.Continuation
