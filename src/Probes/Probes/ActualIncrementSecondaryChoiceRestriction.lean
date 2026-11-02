import Probes.ActualSecondaryOriginalConstruction

/-! The final positivity neighborhood restricts only the domain of the same
secondary chart choice. Host, inverse, scalar cutoff, literal inverse forcing
and finite differential polynomial retain their actual formulas. The same
secondary piece and entire signed sum agree on that open neighborhood. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M Label SubPrimary SubSecondary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def ActualOriginalSecondaryChoice.restrictOpen
    (choice : ActualOriginalSecondaryChoice Ep M m) (G : Set (Ep × M)) (hG : IsOpen G) :
    ActualOriginalSecondaryChoice Ep M m where
  host := choice.host
  chart := choice.chart.restrOpen G hG
  c := choice.c
  cutoff := choice.cutoff

theorem actual_secondary_choice_forcing_restrict
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (choice : ActualOriginalSecondaryChoice Ep M m) (G : Set (Ep × M)) (hG : IsOpen G) :
    actualOriginalSecondaryRealForcing F hF g input length tau delta r (choice.restrictOpen G hG) =
      actualOriginalSecondaryRealForcing F hF g input length tau delta r choice ∧
    actualOriginalSecondaryImagForcing F hF g input length tau delta r (choice.restrictOpen G hG) =
      actualOriginalSecondaryImagForcing F hF g input length tau delta r choice := ⟨rfl,rfl⟩

theorem actual_secondary_choice_piece_restrict
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (choice : ActualOriginalSecondaryChoice Ep M m) (G : Set (Ep × M)) (hG : IsOpen G) :
    EqOn (actualOriginalSecondaryPiece F hF g input length tau delta r (choice.restrictOpen G hG))
      (actualOriginalSecondaryPiece F hF g input length tau delta r choice) G := by
  intro y hy
  have hforcing := actual_secondary_choice_forcing_restrict F hF g input length tau delta r choice G hG
  unfold actualOriginalSecondaryPiece
  rw [hforcing.1,hforcing.2]
  have hsource : (choice.restrictOpen G hG).chart.source = choice.chart.source ∩ G := rfl
  have hchart : ((choice.restrictOpen G hG).chart : Ep × M → X) = choice.chart := rfl
  simp only [actualSecondarySupportedWave,hsource,hchart,mem_inter_iff,hy,and_true]
  rfl

theorem actual_secondary_choice_sum_restrict
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
    (G : Set (Ep × M)) (hG : IsOpen G) :
    EqOn (actualOriginalSecondarySum F hF g input length tau delta
      (fun r a => (choice r a).restrictOpen G hG))
      (actualOriginalSecondarySum F hF g input length tau delta choice) G := by
  intro y hy
  unfold actualOriginalSecondarySum actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
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
  exact actual_secondary_choice_piece_restrict F hF g input length tau delta ((nu,mu),q)
    (choice ⟨((nu,mu),q),h⟩ a) G hG hy

#print axioms actual_secondary_choice_forcing_restrict
#print axioms actual_secondary_choice_piece_restrict
#print axioms actual_secondary_choice_sum_restrict
end GlobalEmbedding.Continuation
