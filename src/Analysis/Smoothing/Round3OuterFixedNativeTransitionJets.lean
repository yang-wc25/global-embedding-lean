import Smoothing.Round3OuterFixedTransitionJets
import Probes.ActualOriginalNativeTransitionJets

/-! Fixed given transitions in the actual product model. -/

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

theorem round3_original_fixed_native_transition_positive_jets
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (j : ℕ) (ell budget : ℝ) (hell : 0 < ell)
    (hfinite : parameterRound2_originalFixedPacketProfile D j ell ≠ ⊤)
    (hbudget : (parameterRound2_originalFixedPacketProfile D j ell).toReal ≤ budget)
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
  have hb := round3_original_fixed_transition_positive_jets D hd j ell budget hell hfinite hbudget
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

#print axioms round3_original_fixed_native_transition_positive_jets
end GlobalEmbedding.Continuation
