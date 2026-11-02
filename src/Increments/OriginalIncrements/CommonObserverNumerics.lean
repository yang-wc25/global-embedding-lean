import OriginalIncrements.ExplicitPrimaryObserverProfiles
import OriginalIncrements.ExplicitMeanProfilePrefixes

/-!
# Common numerical observer costs for the same actual packet

These costs contain no manifold, atlas, chart label, or piece index. The
three low geometric numbers used in this extension are manufactured from
the actual packet. A bound on the native first inverse is kept explicit;
it is a numerical function of the selected spatial margin and low two-jet
bound, never a supremum of constructed higher derivatives.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements

/-- A finite maximum introduces no multiplicity factor. -/
theorem preparedFiniteMaximum_le {I : Type*} [Fintype I]
    (f : I → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ i, f i ≤ B) :
    round3PreparedFiniteMaximum f ≤ B := by
  unfold round3PreparedFiniteMaximum
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hB
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hf i

def commonPhaseInverseBudget (B : ℝ) (Phase : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else
    actualInverseChartMajorant
      (slowInverseMajorant B
        (2^((k-1)+2)*bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase) k)
        (k-1)) (k-1)

theorem commonPhaseInverseBudget_nonneg
    (B : ℝ) (hB : 0 ≤ B) (Phase : ℕ → ℝ)
    (hPhase : ∀ k, 1 ≤ k → 0 ≤ Phase k) (k : ℕ) :
    0 ≤ commonPhaseInverseBudget B Phase k := by
  unfold commonPhaseInverseBudget
  split_ifs
  · exact le_rfl
  · apply zero_le_one.trans (actualInverseChartMajorant_one_le _ _)
    exact slowInverseMajorant_nonneg hB
      (mul_nonneg (by positivity) (zero_le_one.trans
        (one_le_bufferedTransitionPrefix (incrementsCompletionPositiveSlots_nonneg Phase hPhase) k))) _

theorem phaseFirstInverseCost_nonneg {mu Mb : ℝ} (hmu : 0 < mu) (hMb : 0 ≤ Mb) :
    0 ≤ actualEuclideanPhaseInverseJetCost mu Mb 0 0 := by
  have h := actualPhaseInverseConstant_one_le hmu (show 0 ≤ 2*Mb by positivity)
  simp only [actualEuclideanPhaseInverseJetCost,actualInverseChartMajorant,slowInverseMajorant]
  positivity

theorem phase_profiles_le_common
    (mu Mb M B : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb)
    (hM : Mb ≤ M) (hB : actualEuclideanPhaseInverseJetCost mu Mb 0 0 ≤ B)
    (Phase : ℕ → ℝ) (hPhase : ∀ k, 1 ≤ k → 0 ≤ Phase k) (k : ℕ) :
    phaseForwardBudget Mb Phase k ≤ phaseForwardBudget M Phase k ∧
    phaseInverseBudget mu Mb Phase k ≤ commonPhaseInverseBudget B Phase k := by
  constructor
  · unfold phaseForwardBudget
    split_ifs
    · exact le_rfl
    · linarith
    · exact le_rfl
  · unfold phaseInverseBudget commonPhaseInverseBudget
    split_ifs
    · exact le_rfl
    · have hbase := phaseFirstInverseCost_nonneg hmu hMb
      have hJets : 0 ≤ 2^((k-1)+2)*
          bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase) k :=
        mul_nonneg (by positivity) (zero_le_one.trans
          (one_le_bufferedTransitionPrefix (incrementsCompletionPositiveSlots_nonneg Phase hPhase) k))
      unfold actualEuclideanPhaseSampleInverseJetCost
      exact actualInverseChartMajorant_mono_value
        (slowInverseMajorant_nonneg hbase hJets (k-1))
        (slowInverseMajorant_mono_values hbase hJets hB le_rfl (k-1)) (k-1)

def commonObserverForward (m d : ℕ) (M : ℝ)
    (Packet Parameter Spatial : ℕ → ℝ) : ℕ → ℝ :=
  incrementsCompletionPositiveObserverForwardProfile
    (phaseForwardBudget M (phaseFromGivenBudget m d Packet)) Parameter Spatial

def commonObserverInverse (m d : ℕ) (B : ℝ)
    (Packet Parameter Spatial : ℕ → ℝ) : ℕ → ℝ :=
  incrementsCompletionPositiveObserverInverseProfile
    (commonPhaseInverseBudget B (phaseFromGivenBudget m d Packet)) Parameter Spatial

theorem commonObserverForward_nonneg
    (m d : ℕ) (M : ℝ) (hM : 0 ≤ M) (Packet Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k) (j : ℕ) :
    0 ≤ commonObserverForward m d M Packet Parameter Spatial j := by
  apply incrementsCompletionPositiveObserverForwardProfile_nonneg
  · exact fun k _ => phaseForwardBudget_nonneg M hM _
      (fun k _ => phaseFromGivenBudget_nonneg m d Packet k) k
  · exact fun k _ => hParameter k
  · exact fun k _ => hSpatial k

theorem commonObserverInverse_nonneg
    (m d : ℕ) (B : ℝ) (hB : 0 ≤ B) (Packet Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k) (j : ℕ) :
    0 ≤ commonObserverInverse m d B Packet Parameter Spatial j := by
  apply incrementsCompletionPositiveObserverInverseProfile_nonneg
  · exact fun k _ => commonPhaseInverseBudget_nonneg B hB _
      (fun k _ => phaseFromGivenBudget_nonneg m d Packet k) k
  · exact fun k _ => hParameter k
  · exact fun k _ => hSpatial k

theorem commonPhaseInverseBudget_prefix_congr
    (B : ℝ) (Phase Phase' : ℕ → ℝ) (j : ℕ)
    (hPhase : ∀ k, 1 ≤ k → k ≤ j → Phase k = Phase' k) :
    commonPhaseInverseBudget B Phase j = commonPhaseInverseBudget B Phase' j := by
  have hp : bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase) j =
      bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase') j := by
    apply le_antisymm
    · exact positive_prefix_mono Phase Phase' j (fun k hk hkj => (hPhase k hk hkj).le)
    · exact positive_prefix_mono Phase' Phase j (fun k hk hkj => (hPhase k hk hkj).symm.le)
  simp only [commonPhaseInverseBudget,hp]

theorem commonObserverProfiles_prefix_congr
    (m d : ℕ) (M B : ℝ) (Packet Packet' Parameter Parameter' Spatial Spatial' : ℕ → ℝ) (j : ℕ)
    (hPacket : ∀ k, k ≤ j-1 → Packet k = Packet' k)
    (hParameter : ∀ k, 1 ≤ k → k ≤ j → Parameter k = Parameter' k)
    (hSpatial : ∀ k, 1 ≤ k → k ≤ j → Spatial k = Spatial' k) :
    commonObserverForward m d M Packet Parameter Spatial j =
      commonObserverForward m d M Packet' Parameter' Spatial' j ∧
    commonObserverInverse m d B Packet Parameter Spatial j =
      commonObserverInverse m d B Packet' Parameter' Spatial' j := by
  apply incrementsCompletionPositiveObserverProfiles_prefix_congr
  · intro k hk hkj
    exact (phase_profiles_prefix_congr 1 M _ _ k
      (phaseFromGivenBudget_prefix_congr m d k Packet Packet'
        (fun l hl => hPacket l (by omega)))).1
  · intro k hk hkj
    exact commonPhaseInverseBudget_prefix_congr B _ _ k
      (phaseFromGivenBudget_prefix_congr m d k Packet Packet'
        (fun l hl => hPacket l (by omega)))
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

theorem originalBudgetedObserverProfiles_le_common
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (Mb B : ℝ) (hMb : 0 ≤ Mb) (hB : 0 ≤ B)
    (hLow : ∀ nu i, budgeted.Mb nu i ≤ Mb)
    (hBase : ∀ nu i, actualEuclideanPhaseInverseJetCost
      (budgeted.mu nu i) (budgeted.Mb nu i) 0 0 ≤ B)
    (Packet Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k) (j : ℕ) :
    originalBudgetedObserverForward Data theta budgeted Packet Parameter Spatial j ≤
      commonObserverForward m d Mb Packet Parameter Spatial j ∧
    originalBudgetedObserverInverse Data theta budgeted Packet Parameter Spatial j ≤
      commonObserverInverse m d B Packet Parameter Spatial j := by
  let Phase := phaseFromGivenBudget m d Packet
  have hp : ∀ k, 1 ≤ k → 0 ≤ Phase k := fun k _ => phaseFromGivenBudget_nonneg m d Packet k
  have hOwner (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    positive_observer_profiles_mono_prefix
      (phaseForwardBudget (budgeted.Mb nu i) Phase)
      (phaseInverseBudget (budgeted.mu nu i) (budgeted.Mb nu i) Phase) Parameter Spatial
      (phaseForwardBudget Mb Phase) (commonPhaseInverseBudget B Phase) Parameter Spatial j
      (fun k _ => phaseForwardBudget_nonneg _ (budgeted.Mb_nonneg nu i) Phase hp k)
      (fun k _ => phaseInverseBudget_nonneg _ _ (budgeted.mu_pos nu i) (budgeted.Mb_nonneg nu i) Phase hp k)
      (fun k _ => hParameter k) (fun k _ => hSpatial k)
      (fun k _ _ => (phase_profiles_le_common _ _ _ _ (budgeted.mu_pos nu i)
        (budgeted.Mb_nonneg nu i) (hLow nu i) (hBase nu i) Phase hp k).1)
      (fun k _ _ => (phase_profiles_le_common _ _ _ _ (budgeted.mu_pos nu i)
        (budgeted.Mb_nonneg nu i) (hLow nu i) (hBase nu i) Phase hp k).2)
      (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
  constructor
  · apply preparedFiniteMaximum_le
    · exact commonObserverForward_nonneg m d Mb hMb Packet Parameter Spatial hParameter hSpatial j
    · intro a
      exact (hOwner a.1 a.2).1
  · apply preparedFiniteMaximum_le
    · exact commonObserverInverse_nonneg m d B hB Packet Parameter Spatial hParameter hSpatial j
    · intro a
      exact (hOwner a.1 a.2).2

/-- These two scalar bounds are manufactured from the low geometry of the
same packet. They do not read any current high-order input profile. -/
theorem exists_common_packet_low_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta) :
    ∃ B H : ℝ, 0 < B ∧ 0 < H ∧
      (∀ nu i, actualEuclideanPhaseInverseJetCost
        (budgeted.mu nu i) (budgeted.Mb nu i) 0 0 ≤ B) ∧
      (∀ nu i, actualPhaseRefinementFactor (budgeted.mu nu i) (budgeted.Mb nu i) /
        budgeted.buffer nu i ≤ H) := by
  let first := fun a : Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) =>
    actualEuclideanPhaseInverseJetCost (budgeted.mu a.1 a.2) (budgeted.Mb a.1 a.2) 0 0
  let grid := fun a : Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) =>
    actualPhaseRefinementFactor (budgeted.mu a.1 a.2) (budgeted.Mb a.1 a.2) / budgeted.buffer a.1 a.2
  refine ⟨1+round3PreparedFiniteMaximum first,1+round3PreparedFiniteMaximum grid,?_,?_,?_,?_⟩
  · have h := round3PreparedFiniteMaximum_nonneg first
    linarith
  · have h := round3PreparedFiniteMaximum_nonneg grid
    linarith
  · intro nu i
    exact (round3PreparedFiniteMaximum_bound first (nu,i)).trans (by linarith)
  · intro nu i
    exact (round3PreparedFiniteMaximum_bound grid (nu,i)).trans (by linarith)

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.exists_common_packet_low_geometry
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.originalBudgetedObserverProfiles_le_common
