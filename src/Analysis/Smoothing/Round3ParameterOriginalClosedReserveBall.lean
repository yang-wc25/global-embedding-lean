import Smoothing.ParameterRound2OriginalGermReserveBall

/-! For the genuine whole-parameter repair caller, the reserve neighborhood
contains every physical point and hence equals univ. This uses K=P, without
assuming a positive-dimensional native parameter space is compact. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem round3Parameter_original_closed_germ_reserve_ball
    {J : Type*} [Fintype J]
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hAll : D.parameterSet = univ)
    (hLinear : IncrementsOriginalLinearSmoothInputs D)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs D)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs D rho)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation D.atlas D.parameterChart
      D.sourceNormDomain D.parameterNormDomain D.parameterSet i))
    (ell ML : ℝ)
    (hProfile : incrementsOriginalInputProfileWithLinear D 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear D 0 ell).toReal ≤ ML) :
    let S := incrementsOriginalEvaluation D.atlas D.parameterChart
      D.sourceNormDomain D.parameterNormDomain D.parameterSet
    let W := incrementsOriginalParameterRegion D
    let p := parameterRound2_originalTensorGermSeminorm D.atlas D.parameterChart S W hS
      (fun _ _ hy => hy.1) ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional n‖*ML+1))
    0 < radius ∧ ∀ (H : parameterRound2_originalTensorGermSpace D.atlas D.parameterChart S W),
      H.val = D.H → ∀ (input : J → parameterRound2_originalTensorGermSpace D.atlas D.parameterChart S W),
      (∀ a, p 0 (input a-H) < radius) →
      (univ : Set (P × M)) ⊆ W ∧
      (∀ a nu z, z ∈ (univ : Set (P × M)) → z ∈ incrementsOriginalRelativeCutoffSupport D nu →
        rho/4 < D.linearArgument nu z.1 z.2 ((input a).val z.1 z.2)) ∧
      (∀ a z, z ∈ (univ : Set (P × M)) → (input a).val z.1 z.2 =
        incrementsOriginalDecompositionTensor D z.1 z.2 ((input a).val z.1 z.2)) ∧
      (∀ a nu, ContMDiffOn
        ((𝓘(ℝ,EuclideanSpace ℝ (Fin d))).prod (𝓘(ℝ,EuclideanSpace ℝ (Fin n))))
        𝓘(ℝ,ℝ) ∞ (fun z : P × M => D.linearArgument nu z.1 z.2 ((input a).val z.1 z.2))
        ((univ : Set (P × M)) ∩ D.primaryDomain nu)) := by
  intro S W p radius
  have base := parameterRound2_original_germ_reserve_ball (J := J) D hd hLinear hDecomp rho hReserve
    hS ell ML hProfile hML
  refine ⟨base.1,?_⟩
  intro H hH input hclose
  obtain ⟨G,hG,hKG,hGR,hpos,hdec,harg⟩ := base.2 H hH input hclose
  have hGAll : G = univ := Set.eq_univ_of_forall (fun z => hKG (by
    exact ⟨by rw [hAll]; exact mem_univ _,mem_univ _⟩))
  subst G
  exact ⟨hGR,hpos,hdec,harg⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_closed_germ_reserve_ball
