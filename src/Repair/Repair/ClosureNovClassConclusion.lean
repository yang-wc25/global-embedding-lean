import Repair.ClosureNovClassCanonicalRepair

/-! The actual weighted datum, including all native phase and positive
reserve certificates, selected from the proved original-map producer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle Filter
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
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

/-- Source-faithful original conclusion. No generated family, smoothing
packet or private construction is part of its public type. All norms use
the supplied original atlas and full source/parameter sampling domains. -/
structure ClosureNovFullOriginalConclusion
    (g : SourceCollarNovSetup (m+1) d M P) (F0 : P × M → V)
    (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (rho t0 : ℝ) (Fstar : P × M → V)
    (G u : ℕ → P × M → V) (stage : ℕ → ℕ) : Prop where
  initial : G 0 = fun z => Real.sqrt (1-t0^20) • F0 z
  maps_smooth : ∀ j, ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ (G j)
  increments_smooth : ∀ j, ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ (u j)
  actual_update : ∀ j, G (j+1) = fun z => G j z+u j z
  stage_min : ∀ j, 10 ≤ stage j
  stage_step : ∀ j, stage (j+1)=stage j ∨ stage (j+1)=stage j+1
  stages : Tendsto stage atTop atTop
  summable : ∀ z, Summable (fun j => u j z)
  same_series : Fstar = fun z => G 0 z+∑' j, u j z
  joint_smooth : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ Fstar
  slice_smooth : ∀ p, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (fun x => Fstar (p,x))
  exact_metric : ∀ p, inducedMetric (I := 𝓘(ℝ,D)) (fun x => Fstar (p,x)) = metric p
  slice_immersion : ∀ p x, Function.Injective
    (mfderiv 𝓘(ℝ,D) 𝓘(ℝ,V) (fun y => Fstar (p,y)) x)
  phase_regular : ∀ p, PhaseRegular (I := 𝓘(ℝ,D)) (fun x => Fstar (p,x)) (slice_smooth p)
  strict_C2 : paperAtlasCj 2
    (incrementsOriginalMapCoordinates g.source g.parameter.chart (fun z => Fstar z-F0 z))
    g.differentiation g.samples < ENNReal.ofReal rho
  original_norms : ∀ a, Tendsto (fun j => paperAtlasCj a
    (incrementsOriginalMapCoordinates g.source g.parameter.chart (fun z => Fstar z-G j z))
    g.differentiation g.samples) atTop (𝓝 0)
  original_jets : ∀ i a y, y ∈ g.differentiation i →
    Tendsto (fun j => iteratedFDeriv ℝ a
      (incrementsOriginalMapCoordinates g.source g.parameter.chart (G j) i) y) atTop
      (𝓝 (iteratedFDeriv ℝ a (incrementsOriginalMapCoordinates g.source g.parameter.chart Fstar i) y))
  increment_bound : ∀ j, paperAtlasCj (stage j/2)
    (incrementsOriginalMapCoordinates g.source g.parameter.chart (u j)) g.differentiation g.samples ≤
      ENNReal.ofReal ((rho/8)*iterationScale t0 j)

namespace ClosureNovFixedClass.AllowedMap
variable {c : ClosureNovFixedClass m d N M P}

/-- Projection preserves the literal original atlas, map, norm domains,
trajectory and limit. Native phase regularity refers to the same Fstar. -/
theorem full_original_conclusion [CompactSpace M]
    {F0 : P × M → V}
    (h : c.AllowedMap F0)
    {metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x)}
    {rho t0 : ℝ} {Fstar : P × M → V} {G u : ℕ → P × M → V} {stage : ℕ → ℕ}
    (out : RepairOriginalNativeLimitConclusion (h.data) (h.smoothing)
      metric rho t0 Fstar G u stage) :
    ClosureNovFullOriginalConclusion c.geometry F0 metric rho t0 Fstar G u stage where
  initial := out.initial
  maps_smooth := out.maps_smooth
  increments_smooth := out.increments_smooth
  actual_update := out.actual_update
  stage_min := out.stage_min
  stage_step := out.stage_step
  stages := out.stages
  summable := out.summable
  same_series := out.same_series
  joint_smooth := out.joint_smooth
  slice_smooth := out.slice_smooth
  exact_metric := out.exact_metric
  slice_immersion := out.slice_immersion
  phase_regular := out.phase_regular
  strict_C2 := out.strict_C2
  original_norms := out.original_norms
  original_jets := out.original_jets
  increment_bound := out.increment_bound

end ClosureNovFixedClass.AllowedMap
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ClosureNovFixedClass.AllowedMap.full_original_conclusion
