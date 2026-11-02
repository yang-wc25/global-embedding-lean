import Probes.ActualOriginalPhaseProfileJets
import Probes.ActualIncrementOriginalPrimitiveBinding
import Probes.ActualIncrementOriginalCoreFields

/-! Full joint positive jets of the literal four ordered signed phases.
Only the original given total phase profile enters; both true original
primary evaluation conditions are retained. The factor is exactly two,
including the doubled diagonal phases and their negative branch. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators ENNReal
namespace GlobalEmbedding.Continuation

private theorem actual_signed_scalar_jet_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f g : X → ℝ) (z : X) (r : Fin 4) (k : ℕ) (weight B : ℝ)
    (hw : 0 ≤ weight) (hf : ContDiffAt ℝ k f z) (hg : ContDiffAt ℝ k g z)
    (hfb : weight*‖iteratedFDeriv ℝ k f z‖ ≤ B)
    (hgb : weight*‖iteratedFDeriv ℝ k g z‖ ≤ B) :
    weight*‖iteratedFDeriv ℝ k
      (fun y => ![f y+g y,f y-g y,-f y+g y,-f y-g y] r) z‖ ≤ 2*B := by
  have hsum : weight*‖iteratedFDeriv ℝ k (fun y => f y+g y) z‖ ≤ 2*B := by
    rw [fun_iteratedFDeriv_add_apply hf hg]
    calc
      _ ≤ weight*(‖iteratedFDeriv ℝ k f z‖+‖iteratedFDeriv ℝ k g z‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
      _ = weight*‖iteratedFDeriv ℝ k f z‖+weight*‖iteratedFDeriv ℝ k g z‖ := by ring
      _ ≤ B+B := add_le_add hfb hgb
      _ = _ := by ring
  have hdiff (u v : X → ℝ) (hu : ContDiffAt ℝ k u z) (hv : ContDiffAt ℝ k v z)
      (hub : weight*‖iteratedFDeriv ℝ k u z‖ ≤ B)
      (hvb : weight*‖iteratedFDeriv ℝ k v z‖ ≤ B) :
      weight*‖iteratedFDeriv ℝ k (fun y => u y-v y) z‖ ≤ 2*B := by
    rw [fun_iteratedFDeriv_sub_apply hu hv]
    calc
      _ ≤ weight*(‖iteratedFDeriv ℝ k u z‖+‖iteratedFDeriv ℝ k v z‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) hw
      _ = weight*‖iteratedFDeriv ℝ k u z‖+weight*‖iteratedFDeriv ℝ k v z‖ := by ring
      _ ≤ B+B := add_le_add hub hvb
      _ = _ := by ring
  fin_cases r
  · exact hsum
  · exact hdiff f g hf hg hfb hgb
  · change weight*‖iteratedFDeriv ℝ k (fun y => -f y+g y) z‖ ≤ 2*B
    have he : (fun y => -f y+g y) = (fun y => g y-f y) := by funext y; ring
    rw [he]
    exact hdiff g f hg hf hgb hfb
  · change weight*‖iteratedFDeriv ℝ k (fun y => -f y-g y) z‖ ≤ 2*B
    have he : (fun y => -f y-g y) = -(fun y => f y+g y) := by
      funext y
      simp only [Pi.neg_apply]
      ring
    rw [he,iteratedFDeriv_neg_apply,norm_neg]
    exact hsum

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "X" => Ep × Es

def actualOriginalParameterSignedPhase
    (Data : IncrementsOriginalNativeData n d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : (Fin Data.primaryCount × Fin Data.primaryCount) × Fin 4) (z : Ep × M) : ℝ :=
  let p := (Data.parameterChart i.2).symm z.1
  ![Data.phase r.1.1 (p,z.2)+Data.phase r.1.2 (p,z.2),
    Data.phase r.1.1 (p,z.2)-Data.phase r.1.2 (p,z.2),
    -Data.phase r.1.1 (p,z.2)+Data.phase r.1.2 (p,z.2),
    -Data.phase r.1.1 (p,z.2)-Data.phase r.1.2 (p,z.2)] r.2

theorem actual_original_given_signed_phase_positive_jets
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (j : ℕ) (ell budget : ℝ) (hell : 0 < ell)
    (hfinite : actualOriginalGivenInputProfile Data j ell ≠ ⊤)
    (hbudget : (actualOriginalGivenInputProfile Data j ell).toReal ≤ budget)
    (nu mu : Fin Data.primaryCount) (branch : Fin 4)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (k : ℕ) (hk : k ≤ j) (z : X)
    (hnu : parameterTensorModelEquiv n d z ∈ incrementsOriginalPrimaryEvaluation Data nu i)
    (hmu : parameterTensorModelEquiv n d z ∈ incrementsOriginalPrimaryEvaluation Data mu i) :
    let phase := fun y : X => actualOriginalParameterSignedPhase Data i ((nu,mu),branch)
      (y.1,(Data.atlas.chart i.1).symm y.2)
    ell^k*‖iteratedFDeriv ℝ (k+1) phase z‖ ≤
      2*(actualOriginalTotalPhaseJetCost n d j*budget) := by
  intro phase
  let a := parameterTensorModelEquiv n d
  let f := actualOriginalJointPhase Data nu i ∘ a
  let g := actualOriginalJointPhase Data mu i ∘ a
  have hreg (v : Fin Data.primaryCount)
      (hv : a z ∈ incrementsOriginalPrimaryEvaluation Data v i) :
      ContDiffAt ℝ ∞ (actualOriginalJointPhase Data v i ∘ a) z := by
    have hsm := (actualOriginalJointPhase_contDiffOn Data hd hs v i).comp_continuousLinearMap
      a.toContinuousLinearMap
    exact hsm.contDiffAt (((actualOriginalPhaseOpen_open Data hd v i).preimage a.continuous).mem_nhds
      (actualOriginalPhaseOpen_sample Data hd v i hv))
  have hf : ContDiffAt ℝ (k+1) f z := (hreg nu hnu).of_le (by simp)
  have hg : ContDiffAt ℝ (k+1) g z := (hreg mu hmu).of_le (by simp)
  have hfb := actual_original_given_phase_positive_jets Data hd hs j ell budget hell hfinite hbudget nu i k hk z hnu
  have hgb := actual_original_given_phase_positive_jets Data hd hs j ell budget hell hfinite hbudget mu i k hk z hmu
  have he : phase = fun y => ![f y+g y,f y-g y,-f y+g y,-f y-g y] branch := by
    funext y
    change _ = ![Data.phase nu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a y))+
        Data.phase mu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a y)),
      Data.phase nu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a y))-
        Data.phase mu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a y)),
      -Data.phase nu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a y))+
        Data.phase mu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a y)),
      -Data.phase nu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a y))-
        Data.phase mu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a y))] branch
    rw [actual_original_jointPoint_native]
    rfl
  rw [he]
  exact actual_signed_scalar_jet_le f g z branch (k+1) (ell^k)
    (actualOriginalTotalPhaseJetCost n d j*budget) (pow_nonneg hell.le k) hf hg hfb hgb

#print axioms actual_original_given_signed_phase_positive_jets
end GlobalEmbedding.Continuation
