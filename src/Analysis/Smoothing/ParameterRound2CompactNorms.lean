import Smoothing.ParameterRound2OriginalInputs
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Genuine original-norm finiteness from compact coordinate control domains

Source: the full compact source/parameter norm convention and finite-wait
argument in thm:repair. The coordinate functions and differentiation domains
remain original. A real compact coordinate superset inside each open chart
bounds all fixed jets of the same smooth field. This is qualitative higher-
order finiteness, not a new uniform entrance bound on those higher orders.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
noncomputable section

/-- Compact control sets bound every fixed native jet of the same coordinate
field. The compact set is really inside the open differentiation domain. -/
theorem parameterRound2_coordinate_jets_bounded_of_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (O S K : Set E) (hO : IsOpen O)
    (hK : IsCompact K) (hSK : S ⊆ K) (hKO : K ⊆ O)
    (hf : ContDiffOn ℝ ∞ f O) (k : ℕ) :
    BddAbove (Set.range fun x : S => ‖iteratedFDeriv ℝ k f x‖) := by
  have hc : ContinuousOn (iteratedFDeriv ℝ k f) O := by
    apply (hf.continuousOn_iteratedFDerivWithin (m := k) (by simp) hO.uniqueDiffOn).congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen _ hO hx).symm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hKO)
  refine ⟨C, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hC x (hSK x.property)

/-- No high-order entrance condition is needed merely for the finiteness of
any fixed original weighted norm on genuinely compact controlled domains. -/
theorem parameterRound2_paperAtlasWeighted_finite_of_compact
    {ι : Type*} [Fintype ι] {a q : ℕ}
    (f : ι → (Fin a → ℝ) → Fin q → ℝ)
    (O S K : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hK : ∀ i, IsCompact (K i))
    (hSK : ∀ i, S i ⊆ K i) (hKO : ∀ i, K i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (base m : ℕ) (t : ℝ) : paperAtlasWeighted base m t f O S ≠ ⊤ :=
  paperAtlasWeighted_ne_top base m t f O S hO (fun i => (hSK i).trans (hKO i)) hf
    (fun i k _ => parameterRound2_coordinate_jets_bounded_of_compact
      (f i) (O i) (S i) (K i) (hO i) (hK i) (hSK i) (hKO i) (hf i) k)

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The exact source-first original differentiation domain is a real open
product chart, including zero parameter dimension. -/
theorem parameterRound2_originalDifferentiation_open
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (i : Fin A.count × Fin c) : IsOpen (incrementsOriginalDifferentiation A B i) := by
  have heq : incrementsOriginalDifferentiation A B i =
      (parameterTensorModelEquiv n d).symm ⁻¹' ((B i.2).target ×ˢ (A.chart i.1).target) := by
    ext y
    simp only [incrementsOriginalDifferentiation,Set.mem_setOf_eq,Set.mem_preimage,
      parameterTensorModelEquiv_symm_apply,Set.mem_prod]
    exact and_comm
  rw [heq]
  exact ((B i.2).open_target.prod (A.chart i.1).open_target).preimage
    (parameterTensorModelEquiv n d).symm.continuous

/-- On the full parameter manifold the original evaluation domain for compact
source/parameter coordinate pieces is itself compact. The chart membership
conditions are retained and discharged by the actual domain inclusions. -/
theorem parameterRound2_originalEvaluation_univ_compact
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (Omega : Fin A.count → Set (EuclideanSpace ℝ (Fin n)))
    (Q : Fin c → Set (EuclideanSpace ℝ (Fin d)))
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target)
    (i : Fin A.count × Fin c) :
    IsCompact (incrementsOriginalEvaluation A B Omega Q univ i) := by
  have heq : incrementsOriginalEvaluation A B Omega Q univ i =
      (parameterTensorModelEquiv n d).symm ⁻¹' (Q i.2 ×ˢ Omega i.1) := by
    ext y
    simp only [incrementsOriginalEvaluation,Set.mem_setOf_eq,Set.mem_univ,and_true,
      Set.mem_preimage,parameterTensorModelEquiv_symm_apply,Set.mem_prod]
    constructor
    · rintro ⟨hy, hs, hp⟩
      exact ⟨hp, hs⟩
    · rintro ⟨hp, hs⟩
      exact ⟨⟨hOmegaTarget i.1 hs, hQTarget i.2 hp⟩, hs, hp⟩
  rw [heq]
  exact (parameterTensorModelEquiv n d).symm.toHomeomorph.isCompact_preimage.mpr
    ((hQ i.2).prod (hOmega i.1))

/-- Every fixed original map/tensor input order is genuinely finite on the
sampling buffers when the original source and parameter norm pieces are compact.
This supplies qualitative higher-order finiteness; no high-order numerical
entrance budget is added. The original Core itself is not redefined. -/
theorem parameterRound2_original_pair_sampling_finite_of_compact
    {N : ℕ}
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]
    (D : IncrementsOriginalNativeData n d N M P)
    (B : TensorBufferedChartFamily (Fin D.parameterCount) P (EuclideanSpace ℝ (Fin d)))
    (hchart : B.chart = D.parameterChart)
    (hA : IsSmoothBufferedAtlas D.atlas)
    (hB : ∀ i, B.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P)
    (hs : IncrementsOriginalSmoothInputs D) (hopen : D.parameterOpen = univ)
    (hOmega : ∀ i, IsCompact (D.sourceNormDomain i))
    (hQ : ∀ i, IsCompact (D.parameterNormDomain i))
    (hOmegaTarget : ∀ i, D.sourceNormDomain i ⊆ (D.atlas.chart i).target)
    (hQTarget : ∀ i, D.parameterNormDomain i ⊆ (B.chart i).target)
    (hsource : ∀ i, bufferedSamplingCoordinates D.atlas i ⊆ D.sourceNormDomain i)
    (hparameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ D.parameterNormDomain i)
    (j : ℕ) (t : ℝ) :
    parameterLocalOriginalTotalPairWeighted D.atlas B D.F D.H j t
      (tensorLocalOriginalSampling D.atlas B) ≠ ⊤ := by
  have hinputs := parameterRound2_original_full_parameter_inputs D B hchart hA hB hs hopen
  let O := incrementsOriginalDifferentiation D.atlas B.chart
  let S := tensorLocalOriginalSampling D.atlas B
  let K := incrementsOriginalEvaluation D.atlas B.chart
    D.sourceNormDomain D.parameterNormDomain univ
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open D.atlas B.chart
  have hK : ∀ i, IsCompact (K i) := parameterRound2_originalEvaluation_univ_compact
    D.atlas B.chart D.sourceNormDomain D.parameterNormDomain hOmega hQ hOmegaTarget hQTarget
  have hSK : ∀ i, S i ⊆ K i := by
    intro i y hy
    exact ⟨hy.1, hsource i.1 hy.2.1, hparameter i.2 hy.2.2.1, Set.mem_univ _⟩
  have hKO : ∀ i, K i ⊆ O i := fun _ _ hy => hy.1
  exact ENNReal.add_ne_top.mpr
    ⟨parameterRound2_paperAtlasWeighted_finite_of_compact _ O S K hO hK hSK hKO hinputs.2.1 2 j t,
     parameterRound2_paperAtlasWeighted_finite_of_compact _ O S K hO hK hSK hKO hinputs.2.2 0 j t⟩

#print axioms parameterRound2_paperAtlasWeighted_finite_of_compact
#print axioms parameterRound2_originalEvaluation_univ_compact
#print axioms parameterRound2_original_pair_sampling_finite_of_compact
end
end GlobalEmbedding.Continuation
