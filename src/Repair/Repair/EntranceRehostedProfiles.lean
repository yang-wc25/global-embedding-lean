import Repair.ReferenceRehostedChart
import Probes.ActualJointChartTransfer

/-!
# All-order profiles of the actual observing-host chart

The observer chart is the actual atlas transition followed by the fixed
weighted template chart.  Its inverse is the reverse atlas transition
after the template inverse.  The full functions, including order zero,
are retained, so all joint parameter derivatives are controlled on the
same source/target without a new chart selection.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

def repairEntranceCompositionProfile (outer inner : ℕ → ℝ) (j : ℕ) : ℝ :=
  actualFastChartTransferCost inner j*bufferedTransitionPrefix outer j

theorem repairEntranceCompositionProfile_nonneg (outer inner : ℕ → ℝ)
    (hOuter : ∀ j, 0 ≤ outer j) (hInner : ∀ j, 0 ≤ inner j) (j : ℕ) :
    0 ≤ repairEntranceCompositionProfile outer inner j :=
  mul_nonneg (actualFastChartTransferCost_nonneg inner hInner j)
    (zero_le_one.trans (one_le_bufferedTransitionPrefix hOuter j))

private theorem entrance_profile_le_prefix (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {k j : ℕ} (hkj : k ≤ j) : P k ≤ bufferedTransitionPrefix P j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hP l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

/-- Original atlas-transition jets and the actual selected template-chart
jets produce the full observer forward/inverse profiles.  Numerical costs
are fixed before the observer, owner, reference map, and source restriction. -/
theorem repairEntrance_rehosted_chart_profiles
    (OwnForward OwnInverse TransitionForward TransitionInverse : ℕ → ℝ)
    (hOwnForward : ∀ j, 0 ≤ OwnForward j) (hOwnInverse : ∀ j, 0 ≤ OwnInverse j)
    (hTransitionForward : ∀ j, 0 ≤ TransitionForward j)
    (hTransitionInverse : ∀ j, 0 ≤ TransitionInverse j)
    (observer owner : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hOwner : owner ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (own : OpenPartialHomeomorph X X) (U : Set X) (hU : IsOpen U)
    (hOwn : ContDiffOn ℝ ∞ own own.source) (hOwnInv : ContDiffOn ℝ ∞ own.symm own.target)
    (hOwnJets : ∀ j z, z ∈ own.source → ‖iteratedFDeriv ℝ j own z‖ ≤ OwnForward j)
    (hOwnInvJets : ∀ j z, z ∈ own.target → ‖iteratedFDeriv ℝ j own.symm z‖ ≤ OwnInverse j)
    (hTransitionJets : ∀ j z,
      z ∈ (repairReferenceHostTransition (Ep := Ep) observer owner).source →
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition (Ep := Ep) observer owner) z‖ ≤ TransitionForward j)
    (hTransitionInvJets : ∀ j z,
      z ∈ (repairReferenceHostTransition (Ep := Ep) observer owner).target →
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition (Ep := Ep) observer owner).symm z‖ ≤ TransitionInverse j) :
    let native := repairReferenceRehostedChart observer owner own U hU
    (∀ j z, z ∈ native.source → ‖iteratedFDeriv ℝ j native z‖ ≤
      repairEntranceCompositionProfile OwnForward TransitionForward j) ∧
    ∀ j z, z ∈ native.target → ‖iteratedFDeriv ℝ j native.symm z‖ ≤
      repairEntranceCompositionProfile TransitionInverse OwnInverse j := by
  intro native
  let transition := repairReferenceHostTransition (Ep := Ep) observer owner
  have ht := repair_reference_host_transition_smooth (Ep := Ep) observer owner hObserver hOwner
  have hSource (z : X) (hz : z ∈ native.source) :
      z ∈ transition.source ∧ transition z ∈ own.source ∧ z ∈ U :=
    ⟨hz.1.1,hz.1.2,hz.2⟩
  have hTarget (z : X) (hz : z ∈ native.target) :
      z ∈ own.target ∧ own.symm z ∈ transition.target := hz.1
  constructor
  · intro j z hz
    have h := actual_fast_joint_chart_transfer TransitionForward hTransitionForward j transition own
      native.source own.source native.open_source own.open_source
      (ht.1.mono (fun y hy => (hSource y hy).1)) hOwn (fun y hy => (hSource y hy).2.1)
      z hz 1 1 (bufferedTransitionPrefix OwnForward j) zero_lt_one le_rfl (by
        intro k hk
        simp only [one_pow,one_mul]
        exact (hOwnJets k (transition z) (hSource z hz).2.1).trans
          (entrance_profile_le_prefix OwnForward hOwnForward hk)) (by
        intro k hk hkj
        simpa only [one_pow,one_mul] using hTransitionJets k z (hSource z hz).1)
    change ‖iteratedFDeriv ℝ j (own ∘ transition) z‖ ≤
      actualFastChartTransferCost TransitionForward j*bufferedTransitionPrefix OwnForward j
    simpa only [one_pow,one_mul] using h
  · intro j z hz
    have h := actual_fast_joint_chart_transfer OwnInverse hOwnInverse j own.symm transition.symm
      native.target transition.target native.open_target transition.open_target
      (hOwnInv.mono (fun y hy => (hTarget y hy).1)) ht.2 (fun y hy => (hTarget y hy).2)
      z hz 1 1 (bufferedTransitionPrefix TransitionInverse j) zero_lt_one le_rfl (by
        intro k hk
        simp only [one_pow,one_mul]
        exact (hTransitionInvJets k (own.symm z) (hTarget z hz).2).trans
          (entrance_profile_le_prefix TransitionInverse hTransitionInverse hk)) (by
        intro k hk hkj
        simpa only [one_pow,one_mul] using hOwnInvJets k z (hTarget z hz).1)
    change ‖iteratedFDeriv ℝ j (transition.symm ∘ own.symm) z‖ ≤
      actualFastChartTransferCost OwnInverse j*bufferedTransitionPrefix TransitionInverse j
    simpa only [one_pow,one_mul] using h

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_rehosted_chart_profiles
