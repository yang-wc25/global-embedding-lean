import Probes.ActualCoreWeightedJets
import Probes.ActualSpatialJointJets
import Smoothing.TensorParameterCoordinates

/-!
# The frozen original Core supplies native first/Hessian joint profiles

The coordinate map is literally D.F in the given source and parameter
charts. Only original map-coordinate smoothness and finiteness of the
original Core are inputs. The profiles of the actual first and second
spatial derivatives are conclusions, with one explicit model/order cost.
The original evaluation domain is retained, including its parameter set.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [TopologicalSpace P]

def actualOriginalNativeMap (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin N) :=
  D.F ((D.parameterChart i.2).symm z.1,(D.atlas.chart i.1).symm z.2)

theorem actualOriginalNativeMap_eq_coordinate
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    actualOriginalNativeMap D i = (EuclideanSpace.equiv (Fin N) ℝ).symm ∘
      incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F i ∘
        parameterTensorModelEquiv n d := by
  funext z
  have hprod : (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z),
      incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z)) = z :=
    (parameterTensorModelEquiv n d).symm_apply_apply z
  have hp := congrArg Prod.fst hprod
  have hx := congrArg Prod.snd hprod
  dsimp only at hp hx
  simp only [Function.comp_apply,incrementsOriginalMapCoordinates,
    incrementsOriginalJointPoint,ContinuousLinearEquiv.symm_apply_apply]
  rw [hp,hx]
  rfl

def actualOriginalMapJetCost (n d N j : ℕ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
    linearModelFactor (parameterTensorModelEquiv n d) (j+2) *
      coordinateDimensionFactor (n+d) (j+2)

theorem actualOriginalMapJetCost_nonneg (n d N j : ℕ) :
    0 ≤ actualOriginalMapJetCost n d N j :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))
    (coordinateDimensionFactor_nonneg _ _)

theorem actual_original_core_native_shifted_jets
    (D : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hO : ∀ i, IsOpen (incrementsOriginalDifferentiation D.atlas D.parameterChart i))
    (hf : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F i)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i))
    (hfinite : incrementsOriginalCoreInputProfile D j ell ≠ ⊤)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    {k b : ℕ} (hk : k ≤ j) (hb : b ≤ 2)
    {z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)}
    (hz : parameterTensorModelEquiv n d z ∈
      incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet i) :
    ell^k * ‖iteratedFDeriv ℝ (k+b) (actualOriginalNativeMap D i) z‖ ≤
      actualOriginalMapJetCost n d N j * (incrementsOriginalCoreInputProfile D j ell).toReal := by
  have hle := parameterOriginalCore_map_le D j ell
  have hmapfinite := ne_top_of_le_ne_top hfinite hle
  rw [actualOriginalNativeMap_eq_coordinate]
  have h := paperAtlasWeighted_native_shifted_joint_jet_le
    (parameterTensorModelEquiv n d) (EuclideanSpace.equiv (Fin N) ℝ).symm
    2 j ell hell (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F)
    (incrementsOriginalDifferentiation D.atlas D.parameterChart)
    (incrementsOriginalEvaluation D.atlas D.parameterChart
      D.sourceNormDomain D.parameterNormDomain D.parameterSet)
    hO (fun _ _ hx => hx.1) hf hmapfinite i hk hb hz
  exact h.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfinite hle)
    (actualOriginalMapJetCost_nonneg n d N j))

theorem actualOriginalNativeMap_contDiffOn
    (D : IncrementsOriginalNativeData n d N M P)
    (hf : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F i)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i))
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    ContDiffOn ℝ ∞ (actualOriginalNativeMap D i)
      ((parameterTensorModelEquiv n d) ⁻¹'
        incrementsOriginalDifferentiation D.atlas D.parameterChart i) := by
  rw [actualOriginalNativeMap_eq_coordinate]
  exact (EuclideanSpace.equiv (Fin N) ℝ).symm.contDiff.comp_contDiffOn
    ((hf i).comp (parameterTensorModelEquiv n d).contDiff.contDiffOn (fun _ hx => hx))

/-- Same D, same original domains, same Core MAX. Both actual spatial jet
profiles are produced from the original map budget. An open subdomain of
the evaluation set can subsequently be selected for the geometric solver. -/
theorem actual_original_core_first_hessian_joint_profiles
    (D : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hO : ∀ i, IsOpen (incrementsOriginalDifferentiation D.atlas D.parameterChart i))
    (hf : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F i)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i))
    (hfinite : incrementsOriginalCoreInputProfile D j ell ≠ ⊤)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    let O := (parameterTensorModelEquiv n d) ⁻¹'
      incrementsOriginalDifferentiation D.atlas D.parameterChart i
    let S := (parameterTensorModelEquiv n d) ⁻¹'
      incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet i
    let f := actualOriginalNativeMap D i
    let C := actualOriginalMapJetCost n d N j * (incrementsOriginalCoreInputProfile D j ell).toReal
    (ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fun x => f (z.1,x)) z.2) O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
        (fun w => fderiv ℝ (fun x => f (w.1,x)) w.2) z‖ ≤ C) ∧
    (ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fderiv ℝ (fun x => f (z.1,x))) z.2) O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
        (fun w => fderiv ℝ (fderiv ℝ (fun x => f (w.1,x))) w.2) z‖ ≤ C) := by
  dsimp only
  apply actual_spatial_first_second_slow_jets _ _ _
    ((hO i).preimage (parameterTensorModelEquiv n d).continuous)
    (fun _ hx => hx.1) (actualOriginalNativeMap_contDiffOn D hf i) j ell _ hell.le
  intro k hk b hb z hz
  exact actual_original_core_native_shifted_jets D j ell hell hO hf hfinite i hk hb hz

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_core_native_shifted_jets
#print axioms GlobalEmbedding.Continuation.actual_original_core_first_hessian_joint_profiles
