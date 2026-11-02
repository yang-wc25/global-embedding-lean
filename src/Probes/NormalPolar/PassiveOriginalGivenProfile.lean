import NormalPolar.PassiveOriginalTotalPhase
import NormalPolar.PassiveOriginalTransitionNorm
import NormalPolar.PassiveOriginalLinear

/-! The entire unchanged given-input profile of the same literal compact
parameter input. Core, linear coefficients and total phase have cost one;
the actual transition matrix adds precisely the constructed parameter
transition profile. These are input estimates, not hypotheses about any
produced oscillation, first map or repaired map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin 0)) ∞ S]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

variable (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
  (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
  (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
  (hdP : IncrementsOriginalDomainConditions (passiveOriginalData s₀ seed B Q))
  (hd : IncrementsOriginalDomainConditions seed) (hs : IncrementsOriginalSmoothInputs seed)
  (b₀ : Fin seed.parameterCount)
  (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
  (hQ₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ seed.parameterNormDomain b₀)
  (hs₀ : s₀ ∈ seed.parameterSet)
  (hsChart : s₀ ∈ (seed.parameterChart b₀).source) (hB : IsSmoothBufferedAtlas B)
  (hforward : ∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
    𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i))

include hdP hd hs hb₀ hQ₀ hs₀ hsChart hB hforward

theorem passiveOriginal_given_profile_le (j : ℕ) (ell : ℝ) :
    actualOriginalGivenInputProfile (passiveOriginalData s₀ seed B Q) j ell ≤
      actualOriginalGivenInputProfile seed j ell + passiveOriginalParameterTransitionProfile B Q j ell := by
  apply max_le
  · exact ((passiveOriginal_linear_profile_le s₀ seed B Q b₀ hb₀ hQ₀ hs₀ hd.primary_open j ell).trans
      (actualOriginalGivenInputProfile_linear_le seed j ell)).trans
      (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ _ from bot_le))
  · apply max_le
    · apply iSup_le
      intro l
      exact ((passiveOriginal_totalPhase_weighted_le s₀ seed B Q b₀ hd hs hb₀ hQ₀ hs₀ l j ell).trans
        (actualOriginalGivenInputProfile_phase_le seed j ell l)).trans
        (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ _ from bot_le))
    · exact (passiveOriginal_givenTransition_weighted_le s₀ seed B Q hdP hd b₀ hb₀ hQ₀ hs₀ hsChart
        hB hforward j ell).trans
        (add_le_add_left (actualOriginalGivenInputProfile_transition_le seed j ell) _)

/-- A single cost sequence is chosen before the derivative scale. Only
finiteness of the original seed given data is needed to obtain the actual
new input's finite real budget. -/
theorem passiveOriginal_given_profile_uniform_cost
    (hQ : ∀ i, IsCompact (Q i)) (hQT : ∀ i, Q i ⊆ (B.chart i).target) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ j ell, ell ≤ 1 →
      actualOriginalGivenInputProfile seed j ell ≠ ⊤ →
      actualOriginalGivenInputProfile (passiveOriginalData s₀ seed B Q) j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile (passiveOriginalData s₀ seed B Q) j ell).toReal ≤
        (actualOriginalGivenInputProfile seed j ell).toReal + C j := by
  obtain ⟨C,hC,hcost⟩ := passiveOriginalParameterTransitionProfile_uniform_cost B hB hforward Q hQ hQT
  refine ⟨C,hC,?_⟩
  intro j ell hell hseed
  obtain ⟨hpfin,hpbound⟩ := hcost j ell hell
  have hle := passiveOriginal_given_profile_le s₀ seed B Q hdP hd hs b₀ hb₀ hQ₀ hs₀ hsChart hB hforward j ell
  have hfin : actualOriginalGivenInputProfile seed j ell +
      passiveOriginalParameterTransitionProfile B Q j ell ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hseed,hpfin⟩
  refine ⟨ne_top_of_le_ne_top hfin hle,?_⟩
  calc
    _ ≤ (actualOriginalGivenInputProfile seed j ell +
      passiveOriginalParameterTransitionProfile B Q j ell).toReal := ENNReal.toReal_mono hfin hle
    _ = (actualOriginalGivenInputProfile seed j ell).toReal +
      (passiveOriginalParameterTransitionProfile B Q j ell).toReal := ENNReal.toReal_add hseed hpfin
    _ ≤ _ := add_le_add_right hpbound _

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_given_profile_le
#print axioms GlobalEmbedding.Continuation.passiveOriginal_given_profile_uniform_cost
