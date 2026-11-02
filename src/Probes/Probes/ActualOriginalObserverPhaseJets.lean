import Probes.ActualOriginalPhaseProfileJets
import Probes.ActualIncrementOriginalCoreFields
import Smoothing.ParameterGeometryJets

/-! Actual observer spatial phase derivatives, with all later joint parameter
derivatives retained. This directly supplies hGradobsb of the actual mean
profile from the same original given phase differential profile. -/

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

theorem actual_original_observer_phase_spatial_jets
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (hs : IncrementsOriginalSmoothInputs D) (j : ℕ) (ell budget : ℝ) (hell : 0 < ell)
    (hfinite : actualOriginalGivenInputProfile D j ell ≠ ⊤)
    (hbudget : (actualOriginalGivenInputProfile D j ell).toReal ≤ budget)
    (nu : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount)
    (r : Fin n) (k : ℕ) (hk : k ≤ j) (z : X)
    (hz : parameterTensorModelEquiv n d z ∈ incrementsOriginalPrimaryEvaluation D nu i) :
    ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => fderiv ℝ
        (fun x => D.phase nu ((D.parameterChart i.2).symm w.1,(D.atlas.chart i.1).symm x))
        w.2 (EuclideanSpace.single r 1)) z‖ ≤ actualOriginalTotalPhaseJetCost n d j*budget := by
  let a := parameterTensorModelEquiv n d
  let f : X → ℝ := actualOriginalJointPhase D nu i ∘ a
  let U := a ⁻¹' actualOriginalPhaseOpen D nu i
  have hU : IsOpen U := (actualOriginalPhaseOpen_open D hd nu i).preimage a.continuous
  have hf : ContDiffOn ℝ ∞ f U :=
    (actualOriginalJointPhase_contDiffOn D hd hs nu i).comp a.contDiff.contDiffOn (fun _ hw => hw)
  have hzU : z ∈ U := actualOriginalPhaseOpen_sample D hd nu i hz
  have hfeq : f = fun w : X => D.phase nu
      ((D.parameterChart i.2).symm w.1,(D.atlas.chart i.1).symm w.2) := by
    funext w
    simp only [f,a,Function.comp_apply,actualOriginalJointPhase,actual_original_jointPoint_native]
  have hfirst := (incrementsJointSpatialJets_bridge f U hU hf).2.1
  have heval := norm_iteratedFDeriv_clm_apply_const
    (hfirst.contDiffAt (hU.mem_nhds hzU)) (n := k) (c := EuclideanSpace.single r (1:ℝ)) (by simp)
  have hsp := spatial_first_jet_le hU hf hzU k
  have hbound := actual_original_given_phase_positive_jets D hd hs j ell budget hell hfinite hbudget
    nu i k hk z hz
  have hnorm : ‖EuclideanSpace.single r (1:ℝ)‖ = 1 := by simp
  rw [hnorm,one_mul] at heval
  have hfinal := (mul_le_mul_of_nonneg_left (heval.trans hsp) (pow_nonneg hell.le k)).trans hbound
  simpa only [hfeq] using hfinal

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_observer_phase_spatial_jets
