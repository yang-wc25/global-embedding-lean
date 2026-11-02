import Smoothing.ParameterRound2CrossInputJets
import Smoothing.ParameterRound2NativeTensorGermNorms

/-!
# Actual repair cross term in the original tensor coordinates

The two derivatives are the actual source derivatives of the SAME two native
maps. The inverse-chart manifold chain rule proves the coefficient identity.
The fixed component map has norm at most one in every source dimension and
introduces no number of charts. These are the original coordinate slots.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2CrossGermCoordinatesChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2CrossGermCoordinatesIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

theorem parameterRound2_native_slice_contMDiffAt_of_chart
    (e : OpenPartialHomeomorph M Es) (he : e ∈ maximalAtlas 𝓘(ℝ,Es) ∞ M)
    (f : M → Ey) (x : Es) (hx : x ∈ e.target)
    (hf : ContDiffAt ℝ ∞ (f ∘ e.symm) x) :
    ContMDiffAt 𝓘(ℝ,Es) 𝓘(ℝ,Ey) ∞ f (e.symm x) := by
  have hs : e.symm x ∈ e.source := e.symm.map_source hx
  have hc : ContMDiffAt 𝓘(ℝ,Es) 𝓘(ℝ,Es) ∞ e (e.symm x) :=
    (contMDiffOn_of_mem_maximalAtlas he).contMDiffAt (e.open_source.mem_nhds hs)
  have hf' : ContMDiffAt 𝓘(ℝ,Es) 𝓘(ℝ,Ey) ∞ (f ∘ e.symm) (e (e.symm x)) := by
    rw [e.right_inv hx]
    exact hf.contMDiffAt
  apply (hf'.comp (e.symm x) hc).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hs] with y hy
  simp only [Function.comp_apply,e.left_inv hy]

theorem parameterRound2_ambientDerivative_inverseChart_apply_local
    (e : OpenPartialHomeomorph M Es) (he : e ∈ maximalAtlas 𝓘(ℝ, Es) ∞ M)
    (F : M → Ey) (x : Es) (hx : x ∈ e.target)
    (hF : MDifferentiableAt 𝓘(ℝ,Es) 𝓘(ℝ,Ey) F (e.symm x)) (v : Es) :
    tangentSpaceCastModel 𝓘(ℝ, Ey) (F (e.symm x))
      (mfderiv 𝓘(ℝ, Es) 𝓘(ℝ, Ey) F (e.symm x)
        (mfderiv 𝓘(ℝ, Es) 𝓘(ℝ, Es) e.symm x
          ((tangentSpaceCastModel 𝓘(ℝ, Es) x).symm v))) =
      fderiv ℝ (F ∘ e.symm) x v := by
  have hinv : MDifferentiableAt 𝓘(ℝ, Es) 𝓘(ℝ, Es) e.symm x :=
    ((contMDiffOn_symm_of_mem_maximalAtlas he).contMDiffAt
      (e.open_target.mem_nhds hx)).mdifferentiableAt (by simp)
  rw [← mfderiv_comp_apply x hF hinv,mfderiv_eq_fderiv]
  rfl

theorem parameterRound2_nativeMapChart_germ_contDiffOn
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (F : P × M → Ey) (i : Fin A.count × Fin pcount)
    (U : Set (Fin (n+d) → ℝ))
    (hF : ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i) U) :
    ContDiffOn ℝ ∞
      (fun z : Ep × Es => F ((B i.2).symm z.1,(A.chart i.1).symm z.2))
      ((parameterTensorModelEquiv n d) ⁻¹' U) := by
  rw [parameterRound2_nativeMapChart_eq_coordinate A B F i]
  exact (EuclideanSpace.equiv (Fin N) ℝ).symm.contDiff.comp_contDiffOn
    (hF.comp (parameterTensorModelEquiv n d).contDiff.contDiffOn (fun _ hz => hz))

/-- Exact native cross coefficients need only the genuine local chart jets of
both maps. Their values or smoothness away from this neighborhood are unused. -/
theorem parameterRound2_metricCrossTerm_originalCoordinates_germ_eq
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (F U : P × M → Ey)
    (i : Fin A.count × Fin pcount) (y : Fin (n+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i)
    (hF : ContDiffAt ℝ ∞
      (fun z : Ep × Es => F ((B i.2).symm z.1,(A.chart i.1).symm z.2))
      ((parameterTensorModelEquiv n d).symm y))
    (hU : ContDiffAt ℝ ∞
      (fun z : Ep × Es => U ((B i.2).symm z.1,(A.chart i.1).symm z.2))
      ((parameterTensorModelEquiv n d).symm y)) :
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
  have hFc : ContDiffAt ℝ ∞ ((fun z => F (p,z)) ∘ (A.chart i.1).symm) x :=
    hF.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hUc : ContDiffAt ℝ ∞ ((fun z => U (p,z)) ∘ (A.chart i.1).symm) x :=
    hU.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hFd := (parameterRound2_native_slice_contMDiffAt_of_chart (A.chart i.1) (hA.chart_mem i.1)
    (fun z => F (p,z)) x hy.1 hFc).mdifferentiableAt (by simp)
  have hUd := (parameterRound2_native_slice_contMDiffAt_of_chart (A.chart i.1) (hA.chart_mem i.1)
    (fun z => U (p,z)) x hy.1 hUc).mdifferentiableAt (by simp)
  have hFv := parameterRound2_ambientDerivative_inverseChart_apply_local (A.chart i.1) (hA.chart_mem i.1)
    (fun z => F (p,z)) x hy.1 hFd v
  have hFw := parameterRound2_ambientDerivative_inverseChart_apply_local (A.chart i.1) (hA.chart_mem i.1)
    (fun z => F (p,z)) x hy.1 hFd w
  have hUv := parameterRound2_ambientDerivative_inverseChart_apply_local (A.chart i.1) (hA.chart_mem i.1)
    (fun z => U (p,z)) x hy.1 hUd v
  have hUw := parameterRound2_ambientDerivative_inverseChart_apply_local (A.chart i.1) (hA.chart_mem i.1)
    (fun z => U (p,z)) x hy.1 hUd w
  exact congrArg₂ (fun a b : ℝ => a+b)
    (congrArg₂ (fun a b : Ey => inner ℝ a b) hFv hUw)
    (congrArg₂ (fun a b : Ey => inner ℝ a b) hUv hFw)

#print axioms parameterRound2_metricCrossTerm_originalCoordinates_germ_eq
end
end GlobalEmbedding.Continuation
