import Repair.ClosureNovClassCanonicalRepair
import Repair.EndpointCanonicalNumericalSetup
import Repair.ClosureNovClassOpenness
import Repair.ClosureNovSetupNumerical

/-! The coordinate-reference repair theorem. The finite entrance is chosen
before the source manifold, compact parameter manifold, both atlas counts,
the actual reference map and the target metric. All actual factories,
initialization, waits, increments and the common smooth limit are produced
inside the proof. Acceptance remains with the independent maintainer. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation
universe uM uP

/-- Uniform smooth openness for the coordinate best-phase class. The
intrinsic original margin is converted with its fixed auxiliary-to-chart
comparison in the separate intrinsic public theorem. -/
theorem closureNov_original_coordinate_uniform_smooth_openness
    {m d N : ℕ} (c : RepairOriginalNumericalSetup m d N)
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
      [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _) ],
      ClosureNovOriginalOpennessAt (M := M) (P := P) c Jstar rho epsilon t0 := by
  let t0 := c.canonicalInitialScale.{uM,uP} rho hrho
  let epsilon := c.canonicalMetricRadius.{uM,uP} rho hrho
  have hPos := c.canonical_initialScale_metricRadius_pos.{uM,uP} rho hrho
  refine ⟨repairEntranceOriginalMapDepth,epsilon,t0,by decide,by decide,
    hPos.2,hPos.1,c.canonical_initialScale_lt_one rho hrho,?_⟩
  intro M P topologyM topologyP hausdorffM hausdorffP compactP
    chartsM smoothM boundaryM chartsP smoothP auxiliaryNorm
  intro g hg F0 hSmooth hMap hEll hPhase metric hSym hMetricSmooth hPositive hError
  letI : CompactSpace M := g.sourceCompact
  let cActual : ClosureNovFixedClass m d N M P := ⟨c,g,hg⟩
  let h : cActual.AllowedMap F0 := ⟨hSmooth,hMap,hEll,hPhase⟩
  obtain ⟨_,_,_,hFinish⟩ := h.canonical_actual_planned_limit rho hrho
  obtain ⟨Fstar,G,u,stage,out⟩ := hFinish metric hSym hMetricSmooth hPositive hError.le
  exact ⟨Fstar,G,u,stage,h.full_original_conclusion out⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.closureNov_original_coordinate_uniform_smooth_openness
