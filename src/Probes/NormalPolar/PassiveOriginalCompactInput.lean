import NormalPolar.PassiveOriginalSmooth
import NormalPolar.PassiveOriginalGeometry
import NormalPolar.PassiveOriginalLinear
import NormalPolar.PassiveOriginalParameterTransitions

/-! Construction of the actual original input on the full compact physical
parameter manifold. This is an input producer: every native field is the
literal passive extension, and the new legal parameter atlas/Q are actually
constructed. It retains the original source atlas, source norm samples,
labels, Euclidean free normals, immersion constant, decomposition reserve,
and all core-plus-linear budgets. The genuine new parameter transition
costs are finite and selected before the derivative scale. -/

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

theorem passiveOriginal_exists_legal_compact_input
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
        ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ j ell, ell ≤ 1 →
          passiveOriginalParameterTransitionProfile B Q j ell ≠ ⊤ ∧
          (passiveOriginalParameterTransitionProfile B Q j ell).toReal ≤ C j := by
  obtain ⟨B,hB,hforward,Q,hQ⟩ :=
    passiveOriginal_exists_global_forward_parameter_atlas (P := P) (d := d)
  have hInner (i : Fin B.count) (p : P) (hp : p ∈ B.inner i) : B.chart i p ∈ Q i := by
    apply (hQ i).2.2
    apply subset_closure
    apply bufferedInner_subset_sampling B i
    refine ⟨(B.chart i).map_source (B.inner_subset i hp),?_⟩
    change (B.chart i).symm (B.chart i p) ∈ B.inner i
    simpa only [(B.chart i).left_inv (B.inner_subset i hp)] using hp
  obtain ⟨b₀,hb₀,hQ₀⟩ := hd.parameter_cover s₀ hseed
  have hz : seed.parameterChart b₀ s₀ = (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
  have htarget : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target :=
    hz ▸ (seed.parameterChart b₀).map_source hb₀
  have hnorm : (0 : EuclideanSpace ℝ (Fin 0)) ∈ seed.parameterNormDomain b₀ := hz ▸ hQ₀
  have hopen := hd.parameter_subset hseed
  let hdP := passiveOriginalData_domain s₀ seed hd hopen B hB Q (fun i => (hQ i).2.1) hInner
  let hsP := passiveOriginalData_smooth s₀ seed hs hopen b₀ htarget B Q
  refine ⟨B,hB,hforward,Q,hQ,hdP,hsP,
    passiveOriginalData_phaseConditions s₀ seed hd hs hg hopen B Q hdP hsP,
    passiveOriginalData_freeNormalConditions s₀ seed hd hs hn hopen B Q hdP hsP,
    passiveOriginalData_immersion s₀ seed B Q hi hopen,
    passiveOriginalData_ellipticity s₀ seed B Q c he hseed,
    passiveOriginalData_decomposition s₀ seed B Q hc hopen,
    passiveOriginalData_reserve s₀ seed B Q rho hr hopen hseed,
    passiveOriginalData_linearSmooth s₀ seed B Q b₀ hl hopen htarget,?_,?_⟩
  · exact fun j ell => passiveOriginal_linear_profile_le s₀ seed B Q b₀ htarget hnorm hseed
      hd.primary_open j ell
  · exact passiveOriginalParameterTransitionProfile_uniform_cost B hB hforward Q
      (fun i => (hQ i).1) (fun i => (hQ i).2.1)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_exists_legal_compact_input
