import Smoothing.Round3ParameterNativeRestriction
import Probes.ActualIncrementSecondaryChoiceRestriction
import Probes.Round3ParameterSecondaryPullback

/-! Restrict the SAME physical secondary choice to the final mean domain.
Only its chart domain changes; host, inverse map, original cutoff and the
actual forcing formulas remain literal.  Physical restriction and original
parameter pullback commute, and the actual finite sum and U agree on G. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m : ℕ} {P Q M : Type*}
  [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))

def Round3ParameterSecondaryChoice.restrictOpen
    (choice : Round3ParameterSecondaryChoice P M m) (G : Set (P × M)) (hG : IsOpen G) :
    Round3ParameterSecondaryChoice P M m where
  host := choice.host
  chart := choice.chart.restrOpen G hG
  c := choice.c
  cutoff := choice.cutoff

theorem auxBridgeNov_secondary_pullback_restriction_commutes
    (choice : Round3ParameterSecondaryChoice P M m) (B : OpenPartialHomeomorph P Q)
    (G : Set (P × M)) (hG : IsOpen G) :
    (choice.restrictOpen G hG).pullback B =
      (choice.pullback B).restrictOpen (round3ParameterNativeDomain B G)
        (round3Parameter_nativeDomain_open B G hG) := by
  simp only [Round3ParameterSecondaryChoice.restrictOpen,Round3ParameterSecondaryChoice.pullback,
    round3Parameter_chart_restriction_commutes]

theorem auxBridgeNov_secondary_restriction_preserves
    (choice : Round3ParameterSecondaryChoice P M m)
    (hPreserves : Round3ParameterChartPreserves choice.chart)
    (G : Set (P × M)) (hG : IsOpen G) :
    Round3ParameterChartPreserves (choice.restrictOpen G hG).chart :=
  fun z hz => hPreserves z hz.1

section Native
variable {Ep : Type*} [NormedAddCommGroup Ep]

theorem auxBridgeNov_secondary_toNative_restriction
    (choice : Round3ParameterSecondaryChoice Ep M m) (G : Set (Ep × M)) (hG : IsOpen G) :
    (choice.restrictOpen G hG).toNative = choice.toNative.restrictOpen G hG := rfl

theorem auxBridgeNov_secondary_native_restriction_commutes
    (choice : Round3ParameterSecondaryChoice P M m) (B : OpenPartialHomeomorph P Ep)
    (G : Set (P × M)) (hG : IsOpen G) :
    ((choice.restrictOpen G hG).pullback B).toNative =
      (choice.pullback B).toNative.restrictOpen (round3ParameterNativeDomain B G)
        (round3Parameter_nativeDomain_open B G hG) := by
  rw [auxBridgeNov_secondary_pullback_restriction_commutes]
  rfl
end Native

variable {N : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Label SubPrimary SubSecondary : Type*} [Fintype Label] [DecidableEq Label]
  [Fintype SubPrimary] [Fintype SubSecondary]
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem auxBridgeNov_secondary_forcing_restrict
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m) (G : Set (P × M)) (hG : IsOpen G) :
    round3ParameterSecondaryRealForcing F hF g input length tau delta r (choice.restrictOpen G hG) =
      round3ParameterSecondaryRealForcing F hF g input length tau delta r choice ∧
    round3ParameterSecondaryImagForcing F hF g input length tau delta r (choice.restrictOpen G hG) =
      round3ParameterSecondaryImagForcing F hF g input length tau delta r choice := ⟨rfl,rfl⟩

theorem auxBridgeNov_secondary_piece_restrict
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m) (G : Set (P × M)) (hG : IsOpen G) :
    EqOn (round3ParameterSecondaryPiece F hF g input length tau delta r (choice.restrictOpen G hG))
      (round3ParameterSecondaryPiece F hF g input length tau delta r choice) G := by
  intro y hy
  have hforcing := auxBridgeNov_secondary_forcing_restrict F hF g input length tau delta r choice G hG
  unfold round3ParameterSecondaryPiece
  rw [hforcing.1,hforcing.2]
  have hsource : (choice.restrictOpen G hG).chart.source = choice.chart.source ∩ G := rfl
  have hchart : ((choice.restrictOpen G hG).chart : P × M → P × D) = choice.chart := rfl
  simp only [round3ParameterSupportedWave,hsource,hchart,mem_inter_iff,hy,and_true]
  rfl

theorem auxBridgeNov_secondary_sum_restrict
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
    (G : Set (P × M)) (hG : IsOpen G) :
    EqOn (round3ParameterSecondarySum F hF g input length tau delta
      (fun r a => (choice r a).restrictOpen G hG))
      (round3ParameterSecondarySum F hF g input length tau delta choice) G := by
  intro y hy
  unfold round3ParameterSecondarySum actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
  apply Finset.sum_congr rfl
  intro nu hnu
  apply Finset.sum_congr rfl
  intro mu hmu
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro a ha
  have h : nu ≠ mu ∨ q = 0 ∨ q = 3 := (Finset.mem_filter.mp hq).2
  dsimp only
  simp only [dif_pos h]
  exact auxBridgeNov_secondary_piece_restrict F hF g input length tau delta ((nu,mu),q)
    (choice ⟨((nu,mu),q),h⟩ a) G hG hy

theorem auxBridgeNov_increment_secondary_restrict
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
    (G : Set (P × M)) (hG : IsOpen G) :
    EqOn (round3ParameterIncrementMap F hF g input length tau delta
      (fun r a => (choice r a).restrictOpen G hG))
      (round3ParameterIncrementMap F hF g input length tau delta choice) G := by
  intro y hy
  unfold round3ParameterIncrementMap
  rw [auxBridgeNov_secondary_sum_restrict F hF g input length tau delta choice G hG hy]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.auxBridgeNov_secondary_native_restriction_commutes
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_secondary_forcing_restrict
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_secondary_piece_restrict
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_secondary_sum_restrict
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_increment_secondary_restrict
