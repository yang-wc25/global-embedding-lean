import Smoothing.ParameterRound2RepairIdentity
import Smoothing.ParameterGeometryJets
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The actual induced metric in the original joint coordinates

The source directions remain the real inverse-chart tangent vectors. The
manifold chain rule identifies their metric coefficients with the Gram matrix
of the actual source slice derivative. Native joint smoothness of that slice
jet then proves full parameter/source coordinate smoothness of gamma(F).
No metric-coordinate regularity or supplied Gram identity is assumed.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2MetricChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2MetricIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- The true source-chart pullback of the native induced metric is the Gram
matrix of the actual source derivative, by the native manifold chain rule. -/
theorem parameterRound2_inducedMetric_inverseChart_apply
    (e : OpenPartialHomeomorph M Es) (he : e ∈ maximalAtlas 𝓘(ℝ, Es) ∞ M)
    (F : M → Ey) (hF : ContMDiff 𝓘(ℝ, Es) 𝓘(ℝ, Ey) ∞ F)
    (x : Es) (hx : x ∈ e.target) (v w : Es) :
    inducedMetric (I := 𝓘(ℝ, Es)) F (e.symm x)
      (mfderiv 𝓘(ℝ, Es) 𝓘(ℝ, Es) e.symm x
        ((tangentSpaceCastModel 𝓘(ℝ, Es) x).symm v))
      (mfderiv 𝓘(ℝ, Es) 𝓘(ℝ, Es) e.symm x
        ((tangentSpaceCastModel 𝓘(ℝ, Es) x).symm w)) =
      inner ℝ (fderiv ℝ (F ∘ e.symm) x v) (fderiv ℝ (F ∘ e.symm) x w) := by
  have hinv : MDifferentiableAt 𝓘(ℝ, Es) 𝓘(ℝ, Es) e.symm x :=
    ((contMDiffOn_symm_of_mem_maximalAtlas he).contMDiffAt
      (e.open_target.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdf : MDifferentiableAt 𝓘(ℝ, Es) 𝓘(ℝ, Ey) F (e.symm x) :=
    hF.mdifferentiable (by simp) _
  rw [inducedMetric_apply, ← mfderiv_comp_apply x hdf hinv,
    ← mfderiv_comp_apply x hdf hinv, mfderiv_eq_fderiv]
  rfl

/-- Actual native F in a true inverse product chart is jointly smooth. -/
theorem parameterRound2_nativeMapChart_contDiffOn
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F)
    (i : Fin A.count × Fin pcount) :
    ContDiffOn ℝ ∞ (fun z : Ep × Es => F ((B i.2).symm z.1, (A.chart i.1).symm z.2))
      ((B i.2).target ×ˢ (A.chart i.1).target) := by
  let e := (B i.2).prod (A.chart i.1)
  have he : e ∈ maximalAtlas 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hB i.2) (hA.chart_mem i.1)
  letI : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
  have hi : ContMDiffOn 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ep × Es) ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas he
  exact (hF.comp_contMDiffOn hi).contDiffOn

/-- Exact original source-first coefficient formula. Only true spatial
derivatives enter gamma; all later coefficient derivatives remain joint. -/
theorem parameterRound2_inducedMetric_originalCoordinates_eq
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F)
    (i : Fin A.count × Fin pcount) (y : Fin (n + d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i) (k : Fin (n * n)) :
    incrementsOriginalTensorCoordinates A B
        (fun p x => inducedMetric (I := 𝓘(ℝ, Es)) (fun z => F (p,z)) x) i y k =
      inner ℝ
        (fderiv ℝ (fun x => F ((B i.2).symm (incrementsOriginalParameterPoint y),
          (A.chart i.1).symm x)) (incrementsOriginalSourcePoint y)
          (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
        (fderiv ℝ (fun x => F ((B i.2).symm (incrementsOriginalParameterPoint y),
          (A.chart i.1).symm x)) (incrementsOriginalSourcePoint y)
          (EuclideanSpace.single (finProdFinEquiv.symm k).2 1)) := by
  exact parameterRound2_inducedMetric_inverseChart_apply (A.chart i.1) (hA.chart_mem i.1)
    (fun x => F ((B i.2).symm (incrementsOriginalParameterPoint y), x))
    (parameterRound2_native_source_slice_contMDiff hF _) _ hy.1 _ _

/-- Actual induced metrics of jointly smooth native maps satisfy the original
full-joint tensor-coordinate smoothness predicate, including all parameters. -/
theorem parameterRound2_inducedMetric_originalCoordinates_contDiffOn
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F)
    (i : Fin A.count × Fin pcount) :
    ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B
      (fun p x => inducedMetric (I := 𝓘(ℝ, Es)) (fun z => F (p,z)) x) i)
      (incrementsOriginalDifferentiation A B i) := by
  let f := fun z : Ep × Es => F ((B i.2).symm z.1, (A.chart i.1).symm z.2)
  let O := (B i.2).target ×ˢ (A.chart i.1).target
  have hO : IsOpen O := (B i.2).open_target.prod (A.chart i.1).open_target
  have hf : ContDiffOn ℝ ∞ f O := parameterRound2_nativeMapChart_contDiffOn A B hA hB F hF i
  have hDf := (incrementsJointSpatialJets_bridge f O hO hf).2.1
  have hgram : ContDiffOn ℝ ∞ (fun z : Ep × Es => fun k : Fin (n*n) =>
      inner ℝ (fderiv ℝ (fun x => f (z.1,x)) z.2
          (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
        (fderiv ℝ (fun x => f (z.1,x)) z.2
          (EuclideanSpace.single (finProdFinEquiv.symm k).2 1))) O := by
    apply contDiffOn_pi.mpr
    intro k
    exact (hDf.clm_apply contDiffOn_const).inner ℝ (hDf.clm_apply contDiffOn_const)
  have hmap : MapsTo (parameterTensorModelEquiv n d).symm
      (incrementsOriginalDifferentiation A B i) O := fun _ hy => ⟨hy.2, hy.1⟩
  apply (hgram.comp (parameterTensorModelEquiv n d).symm.contDiff.contDiffOn hmap).congr
  intro y hy
  funext k
  exact parameterRound2_inducedMetric_originalCoordinates_eq A B hA F hF i y hy k

#print axioms parameterRound2_inducedMetric_inverseChart_apply
#print axioms parameterRound2_inducedMetric_originalCoordinates_eq
#print axioms parameterRound2_inducedMetric_originalCoordinates_contDiffOn
end
end GlobalEmbedding.Continuation
