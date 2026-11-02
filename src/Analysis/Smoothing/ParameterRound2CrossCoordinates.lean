import Smoothing.ParameterRound2MetricRegularity
import Probes.ActualSecondaryMetricPairing

/-!
# Actual repair cross term in the original tensor coordinates

The two derivatives are the actual source derivatives of the SAME two native
maps. The inverse-chart manifold chain rule proves the coefficient identity.
The fixed component map has norm at most one in every source dimension and
introduces no number of charts. These are the original coordinate slots.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation
noncomputable section

private local instance crossCoordinateTensorSemi (n : ℕ) : SeminormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance crossCoordinateTensorNormed (n : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance crossCoordinateTensorSpace (n : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Fixed component evaluation on the true source Euclidean basis. -/
def parameterRound2_metricComponents (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ]
      (Fin (n*n) → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (finProdFinEquiv.symm k).2 1)).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))

@[simp] theorem parameterRound2_metricComponents_apply (n : ℕ)
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (k : Fin (n*n)) :
    parameterRound2_metricComponents n T k =
      T (EuclideanSpace.single (finProdFinEquiv.symm k).1 1)
        (EuclideanSpace.single (finProdFinEquiv.symm k).2 1) := rfl

theorem parameterRound2_metricComponents_norm_le (n : ℕ) :
    ‖parameterRound2_metricComponents n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg T)).2
  intro k
  change ‖T (EuclideanSpace.single (finProdFinEquiv.symm k).1 1)
    (EuclideanSpace.single (finProdFinEquiv.symm k).2 1)‖ ≤ ‖T‖
  calc
    _ ≤ ‖T (EuclideanSpace.single (finProdFinEquiv.symm k).1 1)‖ *
        ‖EuclideanSpace.single (finProdFinEquiv.symm k).2 (1 : ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖T‖ * ‖EuclideanSpace.single (finProdFinEquiv.symm k).1 (1 : ℝ)‖) *
        ‖EuclideanSpace.single (finProdFinEquiv.symm k).2 (1 : ℝ)‖ :=
      mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
    _ = _ := by simp [EuclideanSpace.single, PiLp.norm_single]

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2CrossChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2CrossIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- The actual inverse-source-chart differential, with all canonical tangent
casts, equals the native Euclidean derivative of the actual chart map. -/
theorem parameterRound2_ambientDerivative_inverseChart_apply
    (e : OpenPartialHomeomorph M Es) (he : e ∈ maximalAtlas 𝓘(ℝ, Es) ∞ M)
    (F : M → Ey) (hF : ContMDiff 𝓘(ℝ, Es) 𝓘(ℝ, Ey) ∞ F)
    (x : Es) (hx : x ∈ e.target) (v : Es) :
    tangentSpaceCastModel 𝓘(ℝ, Ey) (F (e.symm x))
      (mfderiv 𝓘(ℝ, Es) 𝓘(ℝ, Ey) F (e.symm x)
        (mfderiv 𝓘(ℝ, Es) 𝓘(ℝ, Es) e.symm x
          ((tangentSpaceCastModel 𝓘(ℝ, Es) x).symm v))) =
      fderiv ℝ (F ∘ e.symm) x v := by
  have hinv : MDifferentiableAt 𝓘(ℝ, Es) 𝓘(ℝ, Es) e.symm x :=
    ((contMDiffOn_symm_of_mem_maximalAtlas he).contMDiffAt
      (e.open_target.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdf : MDifferentiableAt 𝓘(ℝ, Es) 𝓘(ℝ, Ey) F (e.symm x) :=
    hF.mdifferentiable (by simp) _
  rw [← mfderiv_comp_apply x hdf hinv, mfderiv_eq_fderiv]
  rfl

/-- Exact original coefficient identity for the actual repair cross tensor.
Both metric pairings are retained; there is no squared smoothing error. -/
theorem parameterRound2_metricCrossTerm_originalCoordinates_eq
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A)
    (F U : P × M → Ey)
    (hF : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F)
    (hU : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ U)
    (i : Fin A.count × Fin pcount) (y : Fin (n+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i) :
    incrementsOriginalTensorCoordinates A B
      (fun p x => metricCrossTerm (I := 𝓘(ℝ, Es)) (fun z => F (p,z)) (fun z => U (p,z)) x) i y =
      let z := (parameterTensorModelEquiv n d).symm y
      let DF := fderiv ℝ (fun x => F ((B i.2).symm z.1,(A.chart i.1).symm x)) z.2
      let DU := fderiv ℝ (fun x => U ((B i.2).symm z.1,(A.chart i.1).symm x)) z.2
      parameterRound2_metricComponents n
        (actualMetricJetPairing DF DU + actualMetricJetPairing DU DF) := by
  funext k
  let p := (B i.2).symm (incrementsOriginalParameterPoint y)
  let x := incrementsOriginalSourcePoint y
  let v := EuclideanSpace.single (finProdFinEquiv.symm k).1 (1 : ℝ)
  let w := EuclideanSpace.single (finProdFinEquiv.symm k).2 (1 : ℝ)
  have hFv := parameterRound2_ambientDerivative_inverseChart_apply (A.chart i.1) (hA.chart_mem i.1)
    (fun z => F (p,z)) (parameterRound2_native_source_slice_contMDiff hF p) x hy.1 v
  have hFw := parameterRound2_ambientDerivative_inverseChart_apply (A.chart i.1) (hA.chart_mem i.1)
    (fun z => F (p,z)) (parameterRound2_native_source_slice_contMDiff hF p) x hy.1 w
  have hUv := parameterRound2_ambientDerivative_inverseChart_apply (A.chart i.1) (hA.chart_mem i.1)
    (fun z => U (p,z)) (parameterRound2_native_source_slice_contMDiff hU p) x hy.1 v
  have hUw := parameterRound2_ambientDerivative_inverseChart_apply (A.chart i.1) (hA.chart_mem i.1)
    (fun z => U (p,z)) (parameterRound2_native_source_slice_contMDiff hU p) x hy.1 w
  exact congrArg₂ (fun a b : ℝ => a+b)
    (congrArg₂ (fun a b : Ey => inner ℝ a b) hFv hUw)
    (congrArg₂ (fun a b : Ey => inner ℝ a b) hUv hFw)

#print axioms parameterRound2_metricComponents_norm_le
#print axioms parameterRound2_metricCrossTerm_originalCoordinates_eq
end
end GlobalEmbedding.Continuation
