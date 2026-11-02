import Repair.ReferenceRehostedChart
import Probes.ActualIncrementOriginalSignedPhaseJets

/-!
# Full jets of the actual weighted signed phases

Both phase terms are the literal template covectors composed with their
true owner-to-observer chart transition.  The common cap and original
transition profiles, including order zero, give all four signed branches
one numerical profile.  No bound on a completed signed phase is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

section Linear
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem repair_reference_weighted_linear_jets
    (L : E →L[ℝ] ℝ) (q : X → E) (O : Set X) (hO : IsOpen O)
    (hq : ContDiffOn ℝ ∞ q O)
    (M cap weight : ℝ) (hM : 0 ≤ M) (hCap : 0 ≤ cap)
    (hL : ‖L‖ ≤ M) (hw0 : 0 ≤ weight) (hw : weight ≤ cap)
    (T : ℕ → ℝ) (hT : ∀ j z, z ∈ O → ‖iteratedFDeriv ℝ j q z‖ ≤ T j) :
    ContDiffOn ℝ ∞ (fun z => weight*L (q z)) O ∧
      ∀ j z, z ∈ O → ‖iteratedFDeriv ℝ j (fun z => weight*L (q z)) z‖ ≤ cap*M*T j := by
  have hs : ContDiffOn ℝ ∞ (L ∘ q) O := L.contDiff.comp_contDiffOn hq
  refine ⟨hs.const_smul weight,?_⟩
  intro j z hz
  change ‖iteratedFDeriv ℝ j (fun z => weight • ((L ∘ q) z)) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((hs.contDiffAt (hO.mem_nhds hz)).of_le (by simp)),
    norm_smul,Real.norm_eq_abs,abs_of_nonneg hw0]
  have hp := L.norm_iteratedFDeriv_comp_left (hq.contDiffAt (hO.mem_nhds hz)) (n := j) (by simp)
  calc
    weight*‖iteratedFDeriv ℝ j (L ∘ q) z‖ ≤ cap*‖iteratedFDeriv ℝ j (L ∘ q) z‖ :=
      mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ ≤ cap*(‖L‖*‖iteratedFDeriv ℝ j q z‖) := mul_le_mul_of_nonneg_left hp hCap
    _ ≤ cap*(M*T j) := mul_le_mul_of_nonneg_left
      (mul_le_mul hL (hT j z hz) (norm_nonneg _) hM) hCap
    _ = cap*M*T j := by ring

theorem repair_reference_four_signed_jets
    (f g : X → ℝ) (O : Set X) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (F G : ℕ → ℝ)
    (hF : ∀ j z, z ∈ O → ‖iteratedFDeriv ℝ j f z‖ ≤ F j)
    (hG : ∀ j z, z ∈ O → ‖iteratedFDeriv ℝ j g z‖ ≤ G j)
    (branch : Fin 4) :
    ContDiffOn ℝ ∞ (fun z => ![f z+g z,f z-g z,-f z+g z,-f z-g z] branch) O ∧
      ∀ j z, z ∈ O →
        ‖iteratedFDeriv ℝ j (fun z => ![f z+g z,f z-g z,-f z+g z,-f z-g z] branch) z‖ ≤
          F j+G j := by
  have hsum (j : ℕ) (z : X) (hz : z ∈ O) :
      ‖iteratedFDeriv ℝ j (fun z => f z+g z) z‖ ≤ F j+G j := by
    rw [fun_iteratedFDeriv_add_apply ((hf.contDiffAt (hO.mem_nhds hz)).of_le (by simp))
      ((hg.contDiffAt (hO.mem_nhds hz)).of_le (by simp))]
    exact (norm_add_le _ _).trans (add_le_add (hF j z hz) (hG j z hz))
  have hdiff (j : ℕ) (z : X) (hz : z ∈ O) :
      ‖iteratedFDeriv ℝ j (fun z => f z-g z) z‖ ≤ F j+G j := by
    rw [fun_iteratedFDeriv_sub_apply ((hf.contDiffAt (hO.mem_nhds hz)).of_le (by simp))
      ((hg.contDiffAt (hO.mem_nhds hz)).of_le (by simp))]
    exact (norm_sub_le _ _).trans (add_le_add (hF j z hz) (hG j z hz))
  fin_cases branch
  · exact ⟨hf.add hg,hsum⟩
  · exact ⟨hf.sub hg,hdiff⟩
  · refine ⟨hf.neg.add hg,?_⟩
    intro j z hz
    have he : (fun z => -f z+g z) = -(fun z => f z-g z) := by funext z; simp; ring
    change ‖iteratedFDeriv ℝ j (fun z => -f z+g z) z‖ ≤ _
    rw [he,iteratedFDeriv_neg_apply,norm_neg]
    exact hdiff j z hz
  · refine ⟨hf.neg.sub hg,?_⟩
    intro j z hz
    have he : (fun z => -f z-g z) = -(fun z => f z+g z) := by funext z; simp; ring
    change ‖iteratedFDeriv ℝ j (fun z => -f z-g z) z‖ ≤ _
    rw [he,iteratedFDeriv_neg_apply,norm_neg]
    exact hsum j z hz
end Linear

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

def repairReferenceActualSignedPhase
    (observer left right : OpenPartialHomeomorph M D)
    (xi eta : D →L[ℝ] ℝ) (leftWeight rightWeight : ℝ) (branch : Fin 4) (z : X) : ℝ :=
  let l := leftWeight*xi (left (observer.symm z.2))
  let r := rightWeight*eta (right (observer.symm z.2))
  ![l+r,l-r,-l+r,-l-r] branch

theorem repair_reference_actual_signed_phase_jets
    (observer left right : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (hLeft : left ∈ IsManifold.maximalAtlas I ∞ M)
    (hRight : right ∈ IsManifold.maximalAtlas I ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hSourceLeft : O ⊆ (repairReferenceHostTransition observer left).source)
    (hSourceRight : O ⊆ (repairReferenceHostTransition observer right).source)
    (xi eta : D →L[ℝ] ℝ) (covectorBound cap leftWeight rightWeight : ℝ)
    (hM : 0 ≤ covectorBound) (hCap : 0 ≤ cap)
    (hXi : ‖xi‖ ≤ covectorBound) (hEta : ‖eta‖ ≤ covectorBound)
    (hLeftWeight : 0 ≤ leftWeight ∧ leftWeight ≤ cap)
    (hRightWeight : 0 ≤ rightWeight ∧ rightWeight ≤ cap)
    (TLeft TRight : ℕ → ℝ)
    (hLeftJets : ∀ j z, z ∈ O →
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition observer left) z‖ ≤ TLeft j)
    (hRightJets : ∀ j z, z ∈ O →
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition observer right) z‖ ≤ TRight j)
    (branch : Fin 4) :
    ContDiffOn ℝ ∞ (repairReferenceActualSignedPhase observer left right xi eta leftWeight rightWeight branch) O ∧
      ∀ j z, z ∈ O → ‖iteratedFDeriv ℝ j
        (repairReferenceActualSignedPhase observer left right xi eta leftWeight rightWeight branch) z‖ ≤
          cap*covectorBound*(TLeft j+TRight j) := by
  let L := xi.comp (ContinuousLinearMap.snd ℝ Ep D)
  let R := eta.comp (ContinuousLinearMap.snd ℝ Ep D)
  have hLn : ‖L‖ ≤ covectorBound := (xi.opNorm_comp_le _).trans
    ((mul_le_of_le_one_right (norm_nonneg xi) (ContinuousLinearMap.norm_snd_le ℝ Ep D)).trans hXi)
  have hRn : ‖R‖ ≤ covectorBound := (eta.opNorm_comp_le _).trans
    ((mul_le_of_le_one_right (norm_nonneg eta) (ContinuousLinearMap.norm_snd_le ℝ Ep D)).trans hEta)
  obtain ⟨hl,hLj⟩ := repair_reference_weighted_linear_jets L
    (repairReferenceHostTransition observer left) O hO
    ((repair_reference_host_transition_smooth observer left hObserver hLeft).1.mono hSourceLeft)
    covectorBound cap leftWeight hM hCap hLn hLeftWeight.1 hLeftWeight.2 TLeft hLeftJets
  obtain ⟨hr,hRj⟩ := repair_reference_weighted_linear_jets R
    (repairReferenceHostTransition observer right) O hO
    ((repair_reference_host_transition_smooth observer right hObserver hRight).1.mono hSourceRight)
    covectorBound cap rightWeight hM hCap hRn hRightWeight.1 hRightWeight.2 TRight hRightJets
  obtain ⟨hs,hj⟩ := repair_reference_four_signed_jets
    (fun z => leftWeight*L (repairReferenceHostTransition observer left z))
    (fun z => rightWeight*R (repairReferenceHostTransition observer right z))
    O hO hl hr (fun j => cap*covectorBound*TLeft j) (fun j => cap*covectorBound*TRight j)
    hLj hRj branch
  refine ⟨hs,?_⟩
  intro j z hz
  exact (hj j z hz).trans_eq (by ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_weighted_linear_jets
#print axioms GlobalEmbedding.Continuation.repair_reference_four_signed_jets
#print axioms GlobalEmbedding.Continuation.repair_reference_actual_signed_phase_jets
