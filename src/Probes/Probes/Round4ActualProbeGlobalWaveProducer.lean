import Probes.ActualIncrementPrimaryGlobalSupport

/-! The original global primary channels, with their genuine combined cutoff
supports. This exposes the existing proof from the original global mean binding
without imposing the unrelated tensor decomposition or nonresonance hypotheses.
Only primitive fields, true geometry and actual chart support data are inputs;
no desired output regularity or output support is supplied. -/

noncomputable section
open Manifold Filter
open scoped ContDiff Topology BigOperators ComplexConjugate

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]


variable (F : Ep → M → (EuclideanSpace ℝ (Fin N)))
  (hF : ∀ t, ContMDiff I 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞ (F t))
  (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)

theorem round4_actual_global_primary_wave_regular
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ)
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
    (_hPhase : ∀ ν, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (g.phase ν) W)
    (_hCut : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (g.cutoff ν) (W ∩ primary ν))
    (_hNormal : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞
      (g.normal ν) (W ∩ primary ν))
    (_hArgument : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ g.linearArgument ν z.1 z.2 (input z.1 z.2)) (W ∩ primary ν))
    (_hEta : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ (g.eta ν β) W)
    (_hPositive : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      0 < g.linearArgument ν z.1 z.2 (input z.1 z.2))
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
      (g.chart ν β).target) :
    (∀ ch ν β, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞
      (incrementsGlobalPrimaryExtension F hF g input length tau ch ν β) W) ∧
    (∀ ch ν, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞
      (incrementsGlobalPrimaryAmplitude F hF g input length tau ch ν) W) ∧
    ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞
      (incrementsGlobalPrimaryWave F hF g input length tau) W := by
  have hr := actual_global_primary_extension_regular F hF g input length tau W _hW primary
    _hPrimary _hPrimarySupport _hSourceW _hChart _hChartInv _hInverse _hCombinedSupport
    _hCut _hNormal _hArgument _hEta _hPositive _hG _hJ _hT0 _hA _hB _hSecond
  have he (ch : Bool) (nu : Λ) (beta : Β) : ContMDiffOn ((𝓘(ℝ,Ep)).prod I)
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞
      (incrementsGlobalPrimaryExtension F hF g input length tau ch nu beta) W := by
    cases ch
    · exact (hr nu beta).2.2.2.1
    · exact (hr nu beta).2.2.1
  have ha (ch : Bool) (nu : Λ) : ContMDiffOn ((𝓘(ℝ,Ep)).prod I)
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞
      (incrementsGlobalPrimaryAmplitude F hF g input length tau ch nu) W := by
    intro z hz
    apply ContMDiffWithinAt.sum
    intro beta hb
    exact he ch nu beta z hz
  refine ⟨he,ha,?_⟩
  intro z hz
  apply ContMDiffWithinAt.sum
  intro nu hnu
  exact ((Real.contDiff_cos.comp_contMDiffWithinAt
    ((_hPhase nu z hz).div_const tau)).smul (ha true nu z hz)).sub
      ((Real.contDiff_sin.comp_contMDiffWithinAt
        ((_hPhase nu z hz).div_const tau)).smul (ha false nu z hz))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_global_primary_wave_regular
