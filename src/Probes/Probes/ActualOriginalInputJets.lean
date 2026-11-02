import Probes.ActualOriginalCoreJets
import Smoothing.ParameterRound2CompactNorms
import GlobalEmbedding.Paper.IncrementsOriginalImmersionInputs

/-!
# Native derivative budgets from the original full-parameter input conditions

On the original compact-parameter-manifold route, parameterOpen is univ.
The frozen domain and smooth-input conditions therefore supply the actual
coordinate regularity needed by the Core bridge. No separate desired
first/Hessian regularity or derivative budget is added to the inputs.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

/-- The original parameter chart is used only to select the actual slice.
The source map and its original source chart are unchanged. -/
def actualOriginalParameterSlice (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    (p : EuclideanSpace ℝ (Fin d)) (x : M) : EuclideanSpace ℝ (Fin N) :=
  D.F ((D.parameterChart i.2).symm p,x)

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem actualOriginalParameterSlice_contMDiff
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (hopen : D.parameterOpen = univ)
    (i : Fin D.atlas.count × Fin D.parameterCount) (p : EuclideanSpace ℝ (Fin d)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (actualOriginalParameterSlice D i p) :=
  incrementsOriginal_slice_contMDiff D hd hs _ (by rw [hopen]; exact Set.mem_univ _)

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem actualOriginalNativeMap_source_target
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    {z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)}
    (hz : parameterTensorModelEquiv n d z ∈
      incrementsOriginalDifferentiation D.atlas D.parameterChart i) :
    z.2 ∈ (D.atlas.chart i.1).target := by
  have hprod : (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z),
      incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z)) = z :=
    (parameterTensorModelEquiv n d).symm_apply_apply z
  have hx := congrArg Prod.snd hprod
  dsimp only at hx
  exact hx ▸ hz.1

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem actualOriginalNativeMap_evaluation_members
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    {z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)}
    (hz : parameterTensorModelEquiv n d z ∈
      incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet i) :
    z.2 ∈ D.sourceNormDomain i.1 ∧
      (D.parameterChart i.2).symm z.1 ∈ D.parameterSet := by
  have hprod : (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z),
      incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z)) = z :=
    (parameterTensorModelEquiv n d).symm_apply_apply z
  have hp := congrArg Prod.fst hprod
  have hx := congrArg Prod.snd hprod
  dsimp only at hp hx
  refine ⟨hx ▸ hz.2.1, ?_⟩
  have hset := hz.2.2.2
  change (D.parameterChart i.2).symm
    (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z)) ∈ D.parameterSet at hset
  exact hp ▸ hset

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P] in
/-- The original coordinate ellipticity supplies the literal native first
frame reserve on precisely the original parameter/source evaluation set. -/
theorem actual_original_coordinate_ellipticity
    (D : IncrementsOriginalNativeData n d N M P) (c : ℝ)
    (he : IncrementsOriginalCoordinateEllipticityInputs D c)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    {z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)}
    (hz : parameterTensorModelEquiv n d z ∈
      incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet i)
    (v : EuclideanSpace ℝ (Fin n)) :
    c * ‖v‖^2 ≤ ‖fderiv ℝ (fun x => actualOriginalNativeMap D i (z.1,x)) z.2 v‖^2 := by
  obtain ⟨hsource,hparameter⟩ := actualOriginalNativeMap_evaluation_members D i hz
  exact he.lower _ hparameter i.1 z.2 hsource v

theorem actual_original_full_parameter_core_profiles
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (hopen : D.parameterOpen = univ) (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hfinite : incrementsOriginalCoreInputProfile D j ell ≠ ⊤)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    (U : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
    (_hU : IsOpen U)
    (hUS : U ⊆ (parameterTensorModelEquiv n d) ⁻¹'
      incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet i)
    (budget : ℝ) (hbudget : (incrementsOriginalCoreInputProfile D j ell).toReal ≤ budget) :
    let f := actualOriginalNativeMap D i
    let C := actualOriginalMapJetCost n d N j * budget
    (ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fun x => f (z.1,x)) z.2) U ∧
      ∀ k ≤ j, ∀ z ∈ U, ell^k * ‖iteratedFDeriv ℝ k
        (fun w => fderiv ℝ (fun x => f (w.1,x)) w.2) z‖ ≤ C) ∧
    (ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fderiv ℝ (fun x => f (z.1,x))) z.2) U ∧
      ∀ k ≤ j, ∀ z ∈ U, ell^k * ‖iteratedFDeriv ℝ k
        (fun w => fderiv ℝ (fderiv ℝ (fun x => f (w.1,x))) w.2) z‖ ≤ C) := by
  have hinputs := parameterRound2_original_full_parameter_coordinates D hd hs hopen
  have hp := actual_original_core_first_hessian_joint_profiles D j ell hell
    (parameterRound2_originalDifferentiation_open D.atlas D.parameterChart)
    hinputs.2.1 hfinite i
  have hUO : U ⊆ (parameterTensorModelEquiv n d) ⁻¹'
      incrementsOriginalDifferentiation D.atlas D.parameterChart i :=
    fun _ hz => (hUS hz).1
  have hC := mul_le_mul_of_nonneg_left hbudget (actualOriginalMapJetCost_nonneg n d N j)
  exact ⟨⟨hp.1.1.mono hUO,fun k hk z hz => (hp.1.2 k hk z (hUS hz)).trans hC⟩,
    ⟨hp.2.1.mono hUO,fun k hk z hz => (hp.2.2 k hk z (hUS hz)).trans hC⟩⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_full_parameter_core_profiles
