import Smoothing.ParameterRound2GlobalMeanSupport
import Smoothing.ParameterRound2MeanTensorAlgebra

/-! The literal same-phase grouped mean coefficient is identified with the
SAME original native mean error. This calls the complete original qualitative
binding from its primitive hypotheses, not an assumed mean identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

variable (F : Ep → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)

/-- Subordinate beta amplitudes remain grouped by their original phase nu. -/
def parameterRound2_globalObservedMeanCoefficient
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (e : OpenPartialHomeomorph M D) (z : X)
    (i j : Fin (m+1)) : ℂ :=
  ∑ ν, incrementsMeanRemainder
    (fun _ : Unit => incrementsGlobalObservedLeading F g input e z.1 z.2 ν)
    (fun _ : Unit => incrementsGlobalObservedError F hF g input length tau e z.1 z.2 ν) i j

theorem parameterRound2_actual_globalMean_coordinate_identity

    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (q : ℕ) (_hq : 1 ≤ q) (tau : ℝ) (_htau : 0 < tau)
    (W : Set (Ep × M)) (_hW : IsOpen W) (primary : Λ → Set (Ep × M))
    (_hPrimary : ∀ ν, IsOpen (primary ν))
    (_hPrimarySupport : ∀ ν, incrementsGlobalRelativeSupport W (g.cutoff ν) ⊆ primary ν)
    (_hSourceW : ∀ ν β, (g.chart ν β).source ⊆ W ∩ primary ν)
    (_hChart : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) ∞
      (g.chart ν β) (g.chart ν β).source)
    (_hChartInv : ∀ ν β, ContMDiffOn 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) 
      ((𝓘(ℝ, Ep)).prod I) ∞ (g.chart ν β).symm (g.chart ν β).target)
    (_hInverse : ∀ ν β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1, g.inverse ν β z.1 z.2))
    (_hCombinedSupport : ∀ ν β,
      incrementsGlobalRelativeSupport W (fun z ↦ g.eta ν β z * g.cutoff ν z) ⊆
        (g.chart ν β).source)
    (_hPhase : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (g.phase ν) (W ∩ primary ν))
    (_hCut : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (g.cutoff ν) (W ∩ primary ν))
    (_hNormal : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞
      (g.normal ν) (W ∩ primary ν))
    (_hArgument : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ g.linearArgument ν z.1 z.2 (input z.1 z.2)) (W ∩ primary ν))
    (_hEta : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ (g.eta ν β) W)
    (_hPositive : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      0 < g.linearArgument ν z.1 z.2 (input z.1 z.2))
    (_hUnit : ∀ ν z, z ∈ W → g.cutoff ν z ≠ 0 → ‖g.normal ν z‖ = 1)
    (_hPartition : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      ∀ᶠ w in 𝓝 z, ∑ β, g.eta ν β w = 1)
    (_hSymm : ∀ z ∈ W, (input z.1 z.2).IsSymm)
    (_hDecomp : ∀ z ∈ W, ∀ v w : TangentSpace I z.2,
      ∑ ν, (incrementsGlobalPrimaryB F g input ν z) ^ 2 *
        incrementsGlobalScalarDerivative (I := I) (g.phase ν) z v *
        incrementsGlobalScalarDerivative (I := I) (g.phase ν) z w = input z.1 z.2 v w)
    (_hDouble : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      incrementsGlobalScalarDerivative (I := I) (fun w ↦ g.phase ν w + g.phase ν w) z ≠ 0)
    (_hInteraction : ∀ ν μ, ν ≠ μ → ∀ z,
      z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      z ∈ incrementsGlobalRelativeSupport W (g.cutoff μ) →
      incrementsGlobalScalarDerivative (I := I) (fun w ↦ g.phase ν w + g.phase μ w) z ≠ 0 ∧
      incrementsGlobalScalarDerivative (I := I) (fun w ↦ g.phase ν w - g.phase μ w) z ≠ 0)
    (_hG : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2))
      (g.chart ν β).target)
    (_hJ : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2))
      (g.chart ν β).target)
    (_hT0 : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (_hA : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target)
    (_hB : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target)
    (_hSecond : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 i :
        (EuclideanSpace ℝ (Fin N))))
      (g.chart ν β).target)
    (e : OpenPartialHomeomorph M D)
    (he : ContMDiffOn I 𝓘(ℝ,D) ∞ e e.source)
    (heInv : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
    (z : X) (hz : z.2 ∈ e.target) (hzW : (z.1,e.symm z.2) ∈ W)
    (i j : Fin (m+1)) :
    incrementsGlobalPrimaryMeanError F hF g input (q+2) tau z.1 (e.symm z.2)
      (incrementsGlobalObservationVector (I := I) e z.2 i)
      (incrementsGlobalObservationVector (I := I) e z.2 j) =
      (parameterRound2_globalObservedMeanCoefficient F hF g input (q+2) tau e z i j).re := by
  have h := increments_global_primary_mean_binding F hF g input q _hq tau _htau
    W _hW primary _hPrimary _hPrimarySupport _hSourceW _hChart _hChartInv _hInverse
    _hCombinedSupport _hPhase _hCut _hNormal _hArgument _hEta _hPositive _hUnit
    _hPartition _hSymm _hDecomp _hDouble _hInteraction _hG _hJ _hT0 _hA _hB _hSecond
  have hh := h.2.2 e he heInv z.1 z.2 hz hzW
  have hc := hh.2.2.2.1 i j
  have heq := congrFun (hc.1.symm.trans hc.2) (0 : Fin 1)
  simpa only [parameterRound2_globalObservedMeanCoefficient,incrementsMeanRealCoordinate,
    Finset.sum_apply,Complex.re_sum,ContinuousLinearMap.pi_apply,Complex.reCLM_apply] using heq

#print axioms parameterRound2_actual_globalMean_coordinate_identity
end GlobalEmbedding.Continuation
