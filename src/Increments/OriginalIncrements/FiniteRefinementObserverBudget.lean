import OriginalIncrements.FiniteOriginalObserverBudget
import IncrementsCompletion.OriginalPhasePositiveSupply
import Probes.ActualIncrementOriginalSampling

/-!
# Named observer profiles for the same actual finite refinement

The profile below reads the original Given slot for the actual full joint
phase differential, not a supplied estimate for a constructed chart.  The
finite refinement adapter preserves the native chart, its genuine slices,
the original observation domains and the same host sample.  It will be
applied to the original-data constructor in the next module.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements

def phaseFromGivenBudget (m d : ℕ) (Packet : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else actualOriginalTotalPhaseJetCost (m+1) d (k-1)*max 0 (Packet (k-1))

theorem phaseFromGivenBudget_nonneg (m d : ℕ) (Packet : ℕ → ℝ) (k : ℕ) :
    0 ≤ phaseFromGivenBudget m d Packet k := by
  unfold phaseFromGivenBudget
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (incrementsCompletion_original_phase_jet_cost_nonneg m d (k-1))
      (le_max_left _ _)

theorem phaseFromGivenBudget_prefix_congr
    (m d j : ℕ) (Packet Packet' : ℕ → ℝ)
    (h : ∀ k, k ≤ j-1 → Packet k = Packet' k) :
    ∀ k, 1 ≤ k → k ≤ j →
      phaseFromGivenBudget m d Packet k = phaseFromGivenBudget m d Packet' k := by
  intro k hk hkj
  simp only [phaseFromGivenBudget,h (k-1) (by omega)]

theorem original_observer_profiles_prefix_congr
    (m d j : ℕ) (mu Mb : ℝ) (Packet Packet' Parameter Parameter' Spatial Spatial' : ℕ → ℝ)
    (hPacket : ∀ k, k ≤ j-1 → Packet k = Packet' k)
    (hParameter : ∀ k, 1 ≤ k → k ≤ j → Parameter k = Parameter' k)
    (hSpatial : ∀ k, 1 ≤ k → k ≤ j → Spatial k = Spatial' k) :
    phaseObserverForwardBudget mu Mb (phaseFromGivenBudget m d Packet) Parameter Spatial j =
      phaseObserverForwardBudget mu Mb (phaseFromGivenBudget m d Packet') Parameter' Spatial' j ∧
    phaseObserverInverseBudget mu Mb (phaseFromGivenBudget m d Packet) Parameter Spatial j =
      phaseObserverInverseBudget mu Mb (phaseFromGivenBudget m d Packet') Parameter' Spatial' j := by
  apply incrementsCompletionPositiveObserverProfiles_prefix_congr
  · intro k hk hkj
    exact (phase_profiles_prefix_congr mu Mb _ _ k
      (phaseFromGivenBudget_prefix_congr m d k Packet Packet'
        (fun l hl => hPacket l (hl.trans (Nat.sub_le_sub_right hkj 1))))).1
  · intro k hk hkj
    exact (phase_profiles_prefix_congr mu Mb _ _ k
      (phaseFromGivenBudget_prefix_congr m d k Packet Packet'
        (fun l hl => hPacket l (hl.trans (Nat.sub_le_sub_right hkj 1))))).2
  · exact hParameter
  · exact hSpatial

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

/-- The exact original-domain observer obligation used by the quantitative
finite refinement.  No chart-value estimate occurs, and every observed
order reads the original Given profile only through `j - 1`. -/
def OriginalRefinementObserverBudgets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (owner : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (mu Mb : ℝ) (native : OpenPartialHomeomorph X X) : Prop :=
  ∀ (Packet Parameter Spatial : ℕ → ℝ),
    (∀ k, 1 ≤ k → 0 ≤ Parameter k) → (∀ k, 1 ≤ k → 0 ≤ Spatial k) →
    RepairOriginalTransitionBudgets Data Parameter Spatial →
    ∀ ell, 0 < ell → ell ≤ 1 →
    ∀ (observer : Fin Data.atlas.count × Fin Data.parameterCount) (z : X),
      parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas
        Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
      parameterTensorModelEquiv (m+1) d
        (incrementsCompletionOriginalHostPoint Data owner.2 owner.1 observer z) ∈
        incrementsOriginalPrimaryEvaluation Data nu owner →
      let b := round3ParameterCrossNativeChart (Data.parameterChart owner.2)
        (Data.parameterChart observer.2) native
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans
        (actualHostAdaptedChart (Data.atlas.chart owner.1) b)
      z ∈ t.source → ∀ j, 1 ≤ j →
      (∀ k, k ≤ j-1 → actualOriginalGivenInputProfile Data k ell ≠ ⊤) →
      (∀ k, k ≤ j-1 → (actualOriginalGivenInputProfile Data k ell).toReal ≤ Packet k) →
        ell^(j-1)*‖iteratedFDeriv ℝ j t z‖ ≤
          phaseObserverForwardBudget mu Mb (phaseFromGivenBudget m d Packet) Parameter Spatial j ∧
        ell^(j-1)*‖iteratedFDeriv ℝ j t.symm (t z)‖ ≤
          phaseObserverInverseBudget mu Mb (phaseFromGivenBudget m d Packet) Parameter Spatial j

/-- The scalar finite-refinement certificates imply the actual named
observer budgets at the same original samples.  All such certificates are
manufactured by `original_quantitative_primary_refinement`; none become an
extra original entrance assumption in its strengthened producer. -/
theorem original_refinement_observer_budgets_of_actual_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (owner : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (mu Mb : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb)
    (native : OpenPartialHomeomorph X X) (slices : Ep → OpenPartialHomeomorph M D)
    (data : ActualOriginalHostSliceData (Data.atlas.chart owner.1) native
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart owner.2).symm z.1,z.2)) slices)
    (hFirst : ∀ x ∈ native.source, ‖fderiv ℝ native x‖ ≤ 2*(1+2*Mb))
    (hHigher : ∀ k, 1 ≤ k → ∀ x ∈ native.source,
      ‖iteratedFDeriv ℝ (k+1) native x‖ ≤
        2^(k+2)*‖iteratedFDeriv ℝ (k+1)
          ((fun z : Ep × M => Data.phase nu ((Data.parameterChart owner.2).symm z.1,z.2)) ∘
            (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart owner.1)).symm) x‖)
    (hInverse : ∀ (S : Set X), S ⊆ native.target → ∀ (j : ℕ) (weight Mj : ℝ),
      0 < weight → 0 ≤ Mj →
      (∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ native.symm '' S,
        weight^k*‖iteratedFDeriv ℝ (k+1)
          ((fun z : Ep × M => Data.phase nu ((Data.parameterChart owner.2).symm z.1,z.2)) ∘
            (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart owner.1)).symm) x‖ ≤ Mj) →
      ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ S,
        weight^(k-1)*‖iteratedFDeriv ℝ k native.symm y‖ ≤
          actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j) :
    OriginalRefinementObserverBudgets Data owner nu mu Mb native := by
  intro Packet Parameter Spatial hParameter hSpatial transition ell hell hell1
    observer z hzSample hOwnSample b t hz j hj hFinite hBudget
  let Phase := phaseFromGivenBudget m d Packet
  let point := incrementsCompletionOriginalHostPoint Data owner.2 owner.1 observer z
  let psi := (fun z : Ep × M => Data.phase nu ((Data.parameterChart owner.2).symm z.1,z.2)) ∘
    (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart owner.1)).symm
  have hPhase : ∀ k, 1 ≤ k → 0 ≤ Phase k := fun k _ => phaseFromGivenBudget_nonneg m d Packet k
  have hIdentity : psi = actualOriginalJointPhase Data nu owner ∘ parameterTensorModelEquiv (m+1) d := by
    funext x
    simp only [Function.comp_apply,actualOriginalJointPhase,actual_original_jointPoint_native]
    rfl
  have hPreserves : Round3ParameterChartPreserves native := by
    rcases data with ⟨_,_,_,_,_,_,_,_,_,_,_,_,hf,_,_⟩
    intro x hx
    exact (congrArg Prod.fst (hf hx)).symm
  have hPoint : point ∈ native.source := by
    have hn := (round3ParameterChartPullback_source
      ((Data.parameterChart owner.2).symm.trans (Data.parameterChart observer.2)) native
      (z.1,(Data.atlas.chart owner.1) ((Data.atlas.chart observer.1).symm z.2))).mp hz.2.2
    exact hn.2.1
  have hPhaseJets (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      ell^(k-1)*‖iteratedFDeriv ℝ k psi point‖ ≤ Phase k := by
    have hh := actual_original_given_phase_positive_jets Data hd hs (k-1) ell
      (max 0 (Packet (k-1))) hell (hFinite (k-1) (by omega))
      ((hBudget (k-1) (by omega)).trans (le_max_right _ _)) nu owner
      (k-1) le_rfl point hOwnSample
    rw [Nat.sub_add_cancel hk,← hIdentity] at hh
    simpa only [Phase,phaseFromGivenBudget,ite_eq_right (show k ≠ 0 by omega)] using hh
  have hPositive (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      ell^(k-1)*‖iteratedFDeriv ℝ k native point‖ ≤ phaseForwardBudget Mb Phase k ∧
      ell^(k-1)*‖iteratedFDeriv ℝ k native.symm (native point)‖ ≤ phaseInverseBudget mu Mb Phase k := by
    constructor
    · by_cases hk1 : k = 1
      · subst k
        simpa [phaseForwardBudget,norm_iteratedFDeriv_one] using hFirst point hPoint
      · have hh := hHigher (k-1) (by omega) point hPoint
        rw [Nat.sub_add_cancel hk,show k-1+2 = k+1 by omega] at hh
        calc
          _ ≤ ell^(k-1)*(2^(k+1)*‖iteratedFDeriv ℝ k psi point‖) :=
            mul_le_mul_of_nonneg_left hh (pow_nonneg hell.le _)
          _ = 2^(k+1)*(ell^(k-1)*‖iteratedFDeriv ℝ k psi point‖) := by ring
          _ ≤ 2^(k+1)*Phase k := mul_le_mul_of_nonneg_left (hPhaseJets k hk hkj) (by positivity)
          _ = _ := by simp only [phaseForwardBudget,ite_eq_right (show k ≠ 0 by omega),ite_eq_right hk1]
    · let S : Set X := {native point}
      have hS : S ⊆ native.target := singleton_subset_iff.mpr (native.map_source hPoint)
      have hPrefix0 : 0 ≤ bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase) k :=
        zero_le_one.trans (one_le_bufferedTransitionPrefix
          (incrementsCompletionPositiveSlots_nonneg Phase hPhase) k)
      have hh := hInverse S hS (k-1) ell
        (bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase) k) hell hPrefix0
        (by
          intro l hl hlk x hx
          obtain ⟨y,hy,rfl⟩ := hx
          have hyEq : y = native point := mem_singleton_iff.mp hy
          rw [hyEq,native.left_inv hPoint]
          have hlj : l+1 ≤ j := by omega
          have hp := hPhaseJets (l+1) (by omega) hlj
          simp only [Nat.add_sub_cancel] at hp
          exact hp.trans (phase_positive_prefix_bound Phase hPhase (by omega) (by omega)))
        k hk (by omega) (native point) (mem_singleton _)
      simpa only [phaseInverseBudget,ite_eq_right (show k ≠ 0 by omega)] using hh
  have hObserver := (actual_original_native_evaluation_iff Data hd observer z).mp hzSample
  have hOwn := (actual_original_native_evaluation_iff Data hd owner point).mp hOwnSample.1
  exact incrementsCompletion_original_native_observer_finite_weighted_jets_at
    Data hd owner.2 owner.1 native
    (fun w : Ep × M => Data.phase nu ((Data.parameterChart owner.2).symm w.1,w.2))
    slices data hPreserves (phaseForwardBudget Mb Phase) (phaseInverseBudget mu Mb Phase)
    Parameter Spatial (fun k _ => phaseForwardBudget_nonneg Mb hMb Phase hPhase k)
    (fun k _ => phaseInverseBudget_nonneg mu Mb hmu hMb Phase hPhase k)
    hParameter hSpatial transition ell hell hell1 observer z hObserver.2.1 hObserver.1
    hOwn.2.1 hOwn.1 j hj (fun k hk hkj => (hPositive k hk hkj).1)
    (fun k hk hkj => (hPositive k hk hkj).2) hz

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_observer_profiles_prefix_congr
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_refinement_observer_budgets_of_actual_jets
