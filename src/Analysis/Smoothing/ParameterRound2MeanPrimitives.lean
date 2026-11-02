import Smoothing.ParameterRound2GlobalMeanIdentity
import Smoothing.ParameterRound2WeightedJetNorms
import Probes.ActualIncrementPrimaryGlobalSupport

/-! Primitive qualitative data for the exact native mean-coordinate bridge.
Every field below is an original raw chart, support, smoothness, positivity,
decomposition, or nonresonance condition. No mean identity or output estimate
is a field. This record is consumed immediately by the proved original binding. -/

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

structure ParameterRound2GlobalMeanPrimitives
    (F : Ep → M → V)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M)) : Prop where
  hW : IsOpen W
  hPrimary : ∀ ν, IsOpen (primary ν)
  hPrimarySupport : ∀ ν, incrementsGlobalRelativeSupport W (g.cutoff ν) ⊆ primary ν
  hSourceW : ∀ ν β, (g.chart ν β).source ⊆ W ∩ primary ν
  hChart : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) ∞
      (g.chart ν β) (g.chart ν β).source
  hChartInv : ∀ ν β, ContMDiffOn 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) 
      ((𝓘(ℝ, Ep)).prod I) ∞ (g.chart ν β).symm (g.chart ν β).target
  hInverse : ∀ ν β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1, g.inverse ν β z.1 z.2)
  hCombinedSupport : ∀ ν β,
      incrementsGlobalRelativeSupport W (fun z ↦ g.eta ν β z * g.cutoff ν z) ⊆
        (g.chart ν β).source
  hPhase : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (g.phase ν) (W ∩ primary ν)
  hCut : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (g.cutoff ν) (W ∩ primary ν)
  hNormal : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞
      (g.normal ν) (W ∩ primary ν)
  hArgument : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ g.linearArgument ν z.1 z.2 (input z.1 z.2)) (W ∩ primary ν)
  hEta : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ (g.eta ν β) W
  hPositive : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      0 < g.linearArgument ν z.1 z.2 (input z.1 z.2)
  hUnit : ∀ ν z, z ∈ W → g.cutoff ν z ≠ 0 → ‖g.normal ν z‖ = 1
  hPartition : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      ∀ᶠ w in 𝓝 z, ∑ β, g.eta ν β w = 1
  hSymm : ∀ z ∈ W, (input z.1 z.2).IsSymm
  hDecomp : ∀ z ∈ W, ∀ v w : TangentSpace I z.2,
      ∑ ν, (incrementsGlobalPrimaryB F g input ν z) ^ 2 *
        incrementsGlobalScalarDerivative (I := I) (g.phase ν) z v *
        incrementsGlobalScalarDerivative (I := I) (g.phase ν) z w = input z.1 z.2 v w
  hDouble : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      incrementsGlobalScalarDerivative (I := I) (fun w ↦ g.phase ν w + g.phase ν w) z ≠ 0
  hInteraction : ∀ ν μ, ν ≠ μ → ∀ z,
      z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      z ∈ incrementsGlobalRelativeSupport W (g.cutoff μ) →
      incrementsGlobalScalarDerivative (I := I) (fun w ↦ g.phase ν w + g.phase μ w) z ≠ 0 ∧
      incrementsGlobalScalarDerivative (I := I) (fun w ↦ g.phase ν w - g.phase μ w) z ≠ 0
  hG : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2))
      (g.chart ν β).target
  hJ : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2))
      (g.chart ν β).target
  hT0 : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target
  hA : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target
  hB : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target
  hSecond : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 i :
        (EuclideanSpace ℝ (Fin N))))
      (g.chart ν β).target

theorem parameterRound2_meanPrimitives_coordinate
    (F : Ep → M → V)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (q : ℕ) (hq : 1 ≤ q) (tau : ℝ) (htau : 0 < tau)
    (e : OpenPartialHomeomorph M D)
    (he : ContMDiffOn I 𝓘(ℝ,D) ∞ e e.source)
    (heInv : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
    (z : X) (hz : z.2 ∈ e.target) (hzW : (z.1,e.symm z.2) ∈ W)
    (i j : Fin (m+1)) :
    incrementsGlobalPrimaryMeanError F hF g input (q+2) tau z.1 (e.symm z.2)
      (incrementsGlobalObservationVector (I := I) e z.2 i)
      (incrementsGlobalObservationVector (I := I) e z.2 j) =
      (parameterRound2_globalObservedMeanCoefficient F hF g input (q+2) tau e z i j).re := by
  exact parameterRound2_actual_globalMean_coordinate_identity F hF g input q hq tau htau
    W h.hW primary h.hPrimary h.hPrimarySupport h.hSourceW h.hChart h.hChartInv h.hInverse
    h.hCombinedSupport h.hPhase h.hCut h.hNormal h.hArgument h.hEta h.hPositive h.hUnit
    h.hPartition h.hSymm h.hDecomp h.hDouble h.hInteraction h.hG h.hJ h.hT0 h.hA h.hB h.hSecond
    e he heInv z hz hzW i j

theorem parameterRound2_meanPrimitives_source
    (F : Ep → M → V)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (length : ℕ) (tau : ℝ) :
    ∀ ν β, ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g input tau ν β)
      (g.chart ν β).target := by
  have hh := actual_global_primary_extension_regular F hF g input length tau W h.hW
    primary h.hPrimary h.hPrimarySupport h.hSourceW h.hChart h.hChartInv h.hInverse
    h.hCombinedSupport h.hCut h.hNormal h.hArgument h.hEta h.hPositive
    h.hG h.hJ h.hT0 h.hA h.hB h.hSecond
  exact fun ν β => (hh ν β).2.1

#print axioms parameterRound2_meanPrimitives_source

#print axioms parameterRound2_meanPrimitives_coordinate
end GlobalEmbedding.Continuation
