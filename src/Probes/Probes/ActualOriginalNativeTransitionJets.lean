import Probes.ActualOriginalTransitionProfileJets
import Probes.ActualIncrementOriginalCoreFields

/-! Conjugation of the literal given transition to the native product model.
The parameter inverse remains part of the same map before differentiation.
This supplies the observer-to-host input of the actual adapted chart, using
only the explicit original given differential profile. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "X" => Ep × Es

def actualOriginalNativeGivenTransition
    (D : IncrementsOriginalNativeData n d N M P)
    (i k : Fin D.atlas.count × Fin D.parameterCount) : X → X :=
  (parameterTensorModelEquiv n d).symm ∘ actualOriginalGivenTransition D i k ∘
    parameterTensorModelEquiv n d

def actualOriginalNativeGivenTransitionDomain
    (D : IncrementsOriginalNativeData n d N M P)
    (ik : (Fin D.atlas.count × Fin D.parameterCount) ×
      (Fin D.atlas.count × Fin D.parameterCount)) : Set X :=
  (parameterTensorModelEquiv n d) ⁻¹' actualOriginalGivenTransitionDomain D ik

def actualOriginalNativeGivenTransitionJetCost (n d j : ℕ) : ℝ :=
  ‖(parameterTensorModelEquiv n d).symm.toContinuousLinearMap‖ *
    linearModelFactor (parameterTensorModelEquiv n d) (j+1) *
      actualOriginalGivenTransitionJetCost n d j

theorem actualOriginalNativeGivenTransitionJetCost_nonneg (n d j : ℕ) :
    0 ≤ actualOriginalNativeGivenTransitionJetCost n d j := by
  dsimp only [actualOriginalNativeGivenTransitionJetCost,actualOriginalGivenTransitionJetCost]
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))
    (mul_nonneg (norm_nonneg (actualMatrixOperatorAssembly (n+d))) (coordinateDimensionFactor_nonneg _ _))

theorem actualOriginalNativeGivenTransition_contDiffOn
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (ik : (Fin D.atlas.count × Fin D.parameterCount) ×
      (Fin D.atlas.count × Fin D.parameterCount)) :
    ContDiffOn ℝ ∞ (actualOriginalNativeGivenTransition D ik.1 ik.2)
      (actualOriginalNativeGivenTransitionDomain D ik) :=
  (parameterTensorModelEquiv n d).symm.contDiff.comp_contDiffOn
    ((actualOriginalGivenTransition_contDiffOn D hd ik).comp
      (parameterTensorModelEquiv n d).contDiff.contDiffOn (fun _ hz => hz))

theorem actual_original_given_native_transition_positive_jets
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (j : ℕ) (ell budget : ℝ) (hell : 0 < ell)
    (hfinite : actualOriginalGivenInputProfile D j ell ≠ ⊤)
    (hbudget : (actualOriginalGivenInputProfile D j ell).toReal ≤ budget)
    (ik : (Fin D.atlas.count × Fin D.parameterCount) ×
      (Fin D.atlas.count × Fin D.parameterCount))
    (k : ℕ) (hk : k ≤ j) (z : X)
    (hz : parameterTensorModelEquiv n d z ∈ actualOriginalGivenTransitionSample D ik) :
    ell^k*‖iteratedFDeriv ℝ (k+1) (actualOriginalNativeGivenTransition D ik.1 ik.2) z‖ ≤
      actualOriginalNativeGivenTransitionJetCost n d j*budget := by
  let a := parameterTensorModelEquiv n d
  let f := actualOriginalGivenTransition D ik.1 ik.2
  let U := actualOriginalNativeGivenTransitionDomain D ik
  have hU : IsOpen U := (actualOriginalGivenTransitionDomain_open D ik).preimage a.continuous
  have hzU : z ∈ U := hz.2
  have hf : ContDiffOn ℝ ∞ (f ∘ a) U :=
    (actualOriginalGivenTransition_contDiffOn D hd ik).comp a.contDiff.contDiffOn (fun _ hw => hw)
  have hpost := a.symm.toContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (hf.contDiffAt (hU.mem_nhds hzU)) (n := k+1) (by simp)
  have hpre := norm_iteratedFDeriv_comp_equiv_le a f (k+1) z
  have hb := actual_original_given_transition_positive_jets D hd j ell budget hell hfinite hbudget
    ik k hk (a z) hz
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  have hcost0 : 0 ≤ actualOriginalGivenTransitionJetCost n d j :=
    mul_nonneg (norm_nonneg (actualMatrixOperatorAssembly (n+d))) (coordinateDimensionFactor_nonneg _ _)
  calc
    _ ≤ ell^k*(‖a.symm.toContinuousLinearMap‖*‖iteratedFDeriv ℝ (k+1) (f ∘ a) z‖) :=
      mul_le_mul_of_nonneg_left hpost (pow_nonneg hell.le k)
    _ ≤ ell^k*(‖a.symm.toContinuousLinearMap‖*
        (‖iteratedFDeriv ℝ (k+1) f (a z)‖*linearModelFactor a (k+1))) := by
      gcongr
    _ = ‖a.symm.toContinuousLinearMap‖ *
        (linearModelFactor a (k+1)*(ell^k*‖iteratedFDeriv ℝ (k+1) f (a z)‖)) := by ring
    _ ≤ ‖a.symm.toContinuousLinearMap‖ *
        (linearModelFactor a (j+1)*(actualOriginalGivenTransitionJetCost n d j*budget)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (linearModelFactor_mono a (by omega)) hb
        (by positivity) (linearModelFactor_nonneg _ _)) (norm_nonneg _)
    _ = _ := by dsimp only [actualOriginalNativeGivenTransitionJetCost,a]; ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_given_native_transition_positive_jets
