import IncrementsCompletion.ActivePrimaryMeanRawType
import IncrementsCompletion.OriginalEvaluationPoint
import IncrementsCompletion.AtScaleMeanRawType

/-! Reuse the actual original primitives with the proved local cutoff count.
No primary domain or actual field is replaced. The only changed record field
is the numeric support count, transported through the same original chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "𝓙" => 𝓘(ℝ,Es)
variable {Β : Type*} [Fintype Β]

theorem incrementsCompletion_at_scale_raw_with_sample_count
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (V0 : Set P) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub Lactive : ℕ) (preparedScale : ℝ)
    (prep : ∀ i, IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub preparedScale i)
    (G : Set (P × M)) (hG : IsOpen G)
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (n q j : ℕ) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ) (tau ell Delta : ℝ)
    (hCount : ∀ z ∈ Data.parameterSet ×ˢ (univ : Set M),
      (Finset.univ.filter (fun nu => z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤ Lactive)
    (raw : IncrementsCompletionAtScaleMeanRawProfiles Data hd hs hn g V0 cT Tinv Forward Meta
      Rsub preparedScale prep G hG input inputbar n q j reserve Bnd Mg T tau ell Delta) :
    IncrementsCompletionActiveMeanRawProfiles Data hd hs hn g V0 cT Tinv Forward Meta
      Rsub Lactive preparedScale prep G hG input inputbar n q j reserve Bnd Mg T tau ell Delta := by
  intro i
  let old := Classical.choice (raw i)
  refine ⟨{ old with hCount := ?_ }⟩
  intro z hz
  let w : Ep × M := (z.1,(Data.atlas.chart i.1).symm z.2)
  let W := actualOriginalParameterNeighborhood Data i.2 G
  have hW : IsOpen W := actualOriginalParameterNeighborhood_isOpen Data i.2 G hG
  have hw : w ∈ W := old.hmapWO (old.hSO hz)
  change (Finset.univ.filter (fun nu => w ∈ incrementsGlobalRelativeSupport W
    (fun v : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm v.1,v.2)))).card ≤ Lactive
  have hSample := incrementsCompletion_original_evaluation_parameter Data i z hz
  apply (Finset.card_le_card ?_).trans (hCount ((Data.parameterChart i.2).symm w.1,w.2) hSample)
  intro nu hnu
  have hnuW := (Finset.mem_filter.mp hnu).2
  rw [parameterRound2_global_relativeSupport_eq W hW] at hnuW
  have hphys := round3Parameter_plain_pullback_tsupport
    (round3ParameterProductChart (M := M) (Data.parameterChart i.2)) (Data.cutoff nu) w
    hw.1 hnuW.2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  rw [incrementsBridge_original_relative_support_eq Data hd nu]
  exact ⟨⟨hd.parameter_subset hSample.1,mem_univ _⟩,hphys⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_raw_with_sample_count
