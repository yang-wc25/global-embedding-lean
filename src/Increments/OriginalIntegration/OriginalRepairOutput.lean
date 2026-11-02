import OriginalIntegration.OriginalAtlasNormComparison
import Repair.ClosureNovClassConclusion
import FaithfulCollars.CompactRepairSetup

/-!
# The same actual repair trajectory in the original public norms

The public conclusion below contains the original charts, Omega/Q, map,
metric, one trajectory, one increment sequence and one limit.  It contains
no raw preparation, collar, smoothing packet or generated norm domain.
The transport proof changes only the internal C2 tolerance by an explicit
dimension/transition cost.  It does not change the map or its derivatives.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle Filter
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalIntegration

variable {m d N pc : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
private local instance originalRepairProductChart : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance originalRepairProductManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- Full statement-level repair conclusion on the literal original domains.
The additional displayed trajectory witnesses make the single-sequence
all-orders quantifier in the paper explicit. -/
structure OriginalRepairConclusion
    (A : BufferedAtlas M Es) (B : Fin pc → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin pc → Set Ep)
    (F0 : P × M → V)
    (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (rho t0 : ℝ) (Fstar : P × M → V)
    (G u : ℕ → P × M → V) (stage : ℕ → ℕ) : Prop where
  initial : G 0 = fun z => Real.sqrt (1-t0^20) • F0 z
  maps_smooth : ∀ j, ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ (G j)
  increments_smooth : ∀ j, ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ (u j)
  actual_update : ∀ j, G (j+1) = fun z => G j z+u j z
  stage_min : ∀ j, 10 ≤ stage j
  stage_step : ∀ j, stage (j+1)=stage j ∨ stage (j+1)=stage j+1
  stages : Tendsto stage atTop atTop
  summable : ∀ z, Summable (fun j => u j z)
  same_series : Fstar = fun z => G 0 z+∑' j, u j z
  joint_smooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ Fstar
  slice_smooth : ∀ p, ContMDiff 𝓘(ℝ,Es) 𝓘(ℝ,V) ∞ (fun x => Fstar (p,x))
  exact_metric : ∀ p, inducedMetric (I := 𝓘(ℝ,Es)) (fun x => Fstar (p,x)) = metric p
  slice_immersion : ∀ p x, Function.Injective
    (mfderiv 𝓘(ℝ,Es) 𝓘(ℝ,V) (fun y => Fstar (p,y)) x)
  phase_regular : ∀ p, PhaseRegular (I := 𝓘(ℝ,Es)) (fun x => Fstar (p,x)) (slice_smooth p)
  strict_C2 : paperAtlasCj 2
    (incrementsOriginalMapCoordinates A B (fun z => Fstar z-F0 z))
    (incrementsOriginalDifferentiation A B)
    (incrementsOriginalEvaluation A B Omega Q univ) < ENNReal.ofReal rho
  original_norms : ∀ a, Tendsto (fun j => paperAtlasCj a
    (incrementsOriginalMapCoordinates A B (fun z => Fstar z-G j z))
    (incrementsOriginalDifferentiation A B)
    (incrementsOriginalEvaluation A B Omega Q univ)) atTop (𝓝 0)
  original_jets : ∀ i a y, y ∈ incrementsOriginalDifferentiation A B i →
    Tendsto (fun j => iteratedFDeriv ℝ a (incrementsOriginalMapCoordinates A B (G j) i) y) atTop
      (𝓝 (iteratedFDeriv ℝ a (incrementsOriginalMapCoordinates A B Fstar i) y))

def originalRepairComparison (n d : ℕ) (PT ST : ℕ → ℝ) (j : ℕ) : ℝ :=
  originalCoverNormCost (n+d) (FaithfulRepair.originalJointTransitionProfile n d PT ST) j

theorem originalRepairComparison_pos (n d : ℕ) (PT ST : ℕ → ℝ)
    (hPT : ∀ k, 0 ≤ PT k) (j : ℕ) : 0 < originalRepairComparison n d PT ST j :=
  originalCoverNormCost_pos (n+d) _
    (FaithfulRepair.originalJointTransitionProfile_nonneg n d PT ST hPT) j

def originalRepairInternalRadius (n d : ℕ) (PT ST : ℕ → ℝ) (rho : ℝ) : ℝ :=
  rho/(originalRepairComparison n d PT ST 2+1)

theorem originalRepairInternalRadius_pos (n d : ℕ) (PT ST : ℕ → ℝ)
    (hPT : ∀ k, 0 ≤ PT k) (rho : ℝ) (hrho : 0 < rho) :
    0 < originalRepairInternalRadius n d PT ST rho := by
  exact div_pos hrho (by have := originalRepairComparison_pos n d PT ST hPT 2; linarith)

theorem originalRepairInternalRadius_budget (n d : ℕ) (PT ST : ℕ → ℝ)
    (hPT : ∀ k, 0 ≤ PT k) (rho : ℝ) (hrho : 0 < rho) :
    originalRepairComparison n d PT ST 2 * originalRepairInternalRadius n d PT ST rho < rho := by
  have hC := originalRepairComparison_pos n d PT ST hPT 2
  unfold originalRepairInternalRadius
  rw [← mul_div_assoc, div_lt_iff₀ (by linarith)]
  nlinarith

/-- The same old constructed limit and trajectory acquire their full original
norms through the quantitative cover theorem.  No output-norm estimate is
an input; the only new inputs are the original coordinate transition jets. -/
theorem original_repair_conclusion_of_internal
    (g : SourceCollarNovSetup (m+1) d M P)
    (Omega : Fin g.source.count → Set Es) (Q : Fin g.parameter.count → Set Ep)
    (PT ST : ℕ → ℝ) (hPT : ∀ k, 0 ≤ PT k)
    (hPTransition : FaithfulCollars.OriginalParameterJointTransitions (n := m+1) g.parameter.chart Q PT)
    (hSTransition : FaithfulCollars.OriginalSpatialJointTransitions (d := d) g.source Omega ST)
    {F0 Fstar : P × M → V}
    (hF0 : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ F0)
    {metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x)}
    {rho t0 : ℝ} (hrho : 0 < rho) {G u : ℕ → P × M → V} {stage : ℕ → ℕ}
    (out : ClosureNovFullOriginalConclusion g F0 metric
      (originalRepairInternalRadius (m+1) d PT ST rho) t0 Fstar G u stage) :
    OriginalRepairConclusion g.source g.parameter.chart Omega Q F0 metric rho t0 Fstar G u stage := by
  have hComparison (F : P × M → V)
      (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ F) (j : ℕ) :=
    original_atlas_norm_le_internal_cover g.source g.parameter g.source_smooth g.parameter_smooth
      Omega g.Omega Q g.Q g.source_sampling g.parameter_sampling PT ST hPT
      hPTransition hSTransition F (by simpa only [modelWithCornersSelf_prod] using hF) j
  refine {
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
    strict_C2 := ?_
    original_norms := ?_
    original_jets := out.original_jets }
  · have hmul : ENNReal.ofReal (originalRepairComparison (m+1) d PT ST 2) *
        paperAtlasCj 2 (incrementsOriginalMapCoordinates g.source g.parameter.chart (fun z => Fstar z-F0 z))
          g.differentiation g.samples ≤
        ENNReal.ofReal (originalRepairComparison (m+1) d PT ST 2) *
          ENNReal.ofReal (originalRepairInternalRadius (m+1) d PT ST rho) := by
      gcongr
      exact out.strict_C2.le
    have h := (hComparison (fun z => Fstar z-F0 z) (out.joint_smooth.sub hF0) 2).trans hmul
    rw [← ENNReal.ofReal_mul (originalRepairComparison_pos (m+1) d PT ST hPT 2).le] at h
    exact h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hrho).mpr
      (originalRepairInternalRadius_budget (m+1) d PT ST hPT rho hrho))
  · intro a
    have hlim := ENNReal.Tendsto.const_mul (out.original_norms a)
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (originalRepairComparison (m+1) d PT ST a) ≠ ⊤))
    simp only [mul_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall (fun _ => bot_le)) (Eventually.of_forall (fun j =>
        hComparison (fun z => Fstar z-G j z) (out.joint_smooth.sub (out.maps_smooth j)) a))

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.original_repair_conclusion_of_internal
