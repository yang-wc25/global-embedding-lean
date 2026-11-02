import NormalPolar.PassiveOriginalCompactInput
import NormalPolar.PassiveOriginalGivenProfile

/-! Actual full compact-parameter native input with the complete original
Given profile. The atlas, its compact Q samples and the seed covering
sample are constructed from the original hypotheses. The same passive
native data carries all geometry and every original input estimate.
This constructs new legal parameter data; it does not alter an arbitrarily
prescribed existing B/Q or assume any completed increment. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin 0)) ∞ S]
  [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- One genuine input on all of the physical parameter manifold, with all
original qualitative data and a fixed all-order full Given cost before
any derivative scale. The only quantitative premise in the final estimate
is finiteness of the original seed's given data at that order and scale. -/
theorem passiveOriginal_exists_legal_compact_given_input
    (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
    (hd : IncrementsOriginalDomainConditions seed) (hs : IncrementsOriginalSmoothInputs seed)
    (hseed : s₀ ∈ seed.parameterSet)
    (hg : IncrementsOriginalPhaseConditions seed hd hs)
    (hn : IncrementsOriginalFreeNormalConditions seed hd hs)
    (hi : IncrementsOriginalSliceImmersionInputs seed)
    (c rho : ℝ) (he : IncrementsOriginalCoordinateEllipticityInputs seed c)
    (hc : IncrementsOriginalQualitativeDecompositionInputs seed)
    (hr : IncrementsOriginalDecompositionReserveInputs seed rho)
    (hl : IncrementsOriginalLinearSmoothInputs seed) :
    ∃ B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)),
      IsSmoothBufferedAtlas B ∧
      (∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
        𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i)) ∧
      ∃ Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)),
      (∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
        closure (bufferedSamplingCoordinates B i) ⊆ Q i) ∧
      let D := passiveOriginalData s₀ seed B Q
      ∃ hdP : IncrementsOriginalDomainConditions D,
      ∃ hsP : IncrementsOriginalSmoothInputs D,
        IncrementsOriginalPhaseConditions D hdP hsP ∧
        IncrementsOriginalFreeNormalConditions D hdP hsP ∧
        IncrementsOriginalSliceImmersionInputs D ∧
        IncrementsOriginalCoordinateEllipticityInputs D c ∧
        IncrementsOriginalQualitativeDecompositionInputs D ∧
        IncrementsOriginalDecompositionReserveInputs D rho ∧
        IncrementsOriginalLinearSmoothInputs D ∧
        (∀ j ell, incrementsOriginalInputProfileWithLinear D j ell ≤
          incrementsOriginalInputProfileWithLinear seed j ell) ∧
        (∀ j ell, actualOriginalGivenInputProfile D j ell ≤
          actualOriginalGivenInputProfile seed j ell + passiveOriginalParameterTransitionProfile B Q j ell) ∧
        ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ j ell, ell ≤ 1 →
          actualOriginalGivenInputProfile seed j ell ≠ ⊤ →
          actualOriginalGivenInputProfile D j ell ≠ ⊤ ∧
          (actualOriginalGivenInputProfile D j ell).toReal ≤
            (actualOriginalGivenInputProfile seed j ell).toReal + C j := by
  obtain ⟨B,hB,hforward,Q,hQ,hdP,hsP,hgP,hnP,hiP,heP,hcP,hrP,hlP,hcore,hparam⟩ :=
    passiveOriginal_exists_legal_compact_input (P := P) (d := d)
      s₀ seed hd hs hseed hg hn hi c rho he hc hr hl
  obtain ⟨b₀,hb₀,hQ₀⟩ := hd.parameter_cover s₀ hseed
  have hz : seed.parameterChart b₀ s₀ = (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
  have htarget : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target :=
    hz ▸ (seed.parameterChart b₀).map_source hb₀
  have hnorm : (0 : EuclideanSpace ℝ (Fin 0)) ∈ seed.parameterNormDomain b₀ := hz ▸ hQ₀
  refine ⟨B,hB,hforward,Q,hQ,hdP,hsP,hgP,hnP,hiP,heP,hcP,hrP,hlP,hcore,?_,?_⟩
  · exact passiveOriginal_given_profile_le s₀ seed B Q hdP hd hs b₀ htarget hnorm hseed hb₀ hB hforward
  · exact passiveOriginal_given_profile_uniform_cost s₀ seed B Q hdP hd hs b₀ htarget hnorm hseed hb₀
      hB hforward (fun i => (hQ i).1) (fun i => (hQ i).2.1)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_exists_legal_compact_given_input
