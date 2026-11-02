import Smoothing.ParameterRound2WeightedJetNorms
import Probes.ActualIncrementOriginalCoordinateJets
import Smoothing.WeightedActualOperations

/-! Original MAX norms from a genuine cover by native charts.  Each original
sample may use a different adapted piece.  The physical field is fixed and
the chart equality holds on open germs, so the same derivatives are bounded.
Neither the number of pieces nor the number of original charts occurs in
the constant.  Original differentiation and evaluation sets are retained.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation

theorem round3_original_weighted_norm_from_native_open_cover
    {I A X : Type*} [Fintype I] [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a N : ℕ} (j : ℕ) (ell K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hK : 0 ≤ K)
    (T : ℕ → ℝ) (hT : ∀ l, 0 ≤ T l)
    (f : I → (Fin a → ℝ) → Fin N → ℝ)
    (D S : I → Set (Fin a → ℝ)) (hD : ∀ i, IsOpen (D i))
    (U : I → A → Set (Fin a → ℝ)) (O : I → A → Set X)
    (g : I → A → X → EuclideanSpace ℝ (Fin N))
    (phi : I → A → (Fin a → ℝ) → X)
    (hU : ∀ i b, IsOpen (U i b)) (hO : ∀ i b, IsOpen (O i b))
    (hUD : ∀ i b, U i b ⊆ D i)
    (hCover : ∀ i y, y ∈ S i → ∃ b, y ∈ U i b)
    (hg : ∀ i b, ContDiffOn ℝ ∞ (g i b) (O i b))
    (hphi : ∀ i b, ContDiffOn ℝ ∞ (phi i b) (U i b))
    (hMap : ∀ i b, MapsTo (phi i b) (U i b) (O i b))
    (hEq : ∀ i b, EqOn (f i)
      ((EuclideanSpace.equiv (Fin N) ℝ) ∘ g i b ∘ phi i b) (U i b))
    (hJets : ∀ i b k, k ≤ j → ∀ y ∈ S i ∩ U i b,
      ell^k*‖iteratedFDeriv ℝ k (g i b) (phi i b y)‖ ≤ K)
    (hTransition : ∀ i b k, 1 ≤ k → k ≤ j → ∀ y ∈ S i ∩ U i b,
      ell^(k-1)*‖iteratedFDeriv ℝ k (phi i b) y‖ ≤ T k) :
    (∀ i, ContDiffOn ℝ ∞ (f i) (⋃ b, U i b)) ∧
    paperAtlasWeighted 0 j ell f D S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j ell f D S).toReal ≤
      (j+1)*(‖(EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap‖*
        actualFastChartTransferPrefix T j*K) := by
  let cy := (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  let C := ‖cy‖*actualFastChartTransferPrefix T j*K
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (norm_nonneg _) (actualFastChartTransferPrefix_nonneg T hT j)) hK
  let V := fun i => ⋃ b, U i b
  have hV : ∀ i, IsOpen (V i) := fun i => isOpen_iUnion (hU i)
  have hSV : ∀ i, S i ⊆ V i := by
    intro i y hy
    obtain ⟨b,hb⟩ := hCover i y hy
    exact mem_iUnion.mpr ⟨b,hb⟩
  have hVD : ∀ i, V i ⊆ D i := by
    intro i y hy
    obtain ⟨b,hb⟩ := mem_iUnion.mp hy
    exact hUD i b hb
  have hf (i : I) : ContDiffOn ℝ ∞ (f i) (V i) :=
    ContDiffOn.iUnion_of_isOpen (fun b =>
      (cy.contDiff.comp_contDiffOn ((hg i b).comp (hphi i b) (hMap i b))).congr (hEq i b)) (hU i)
  have hb (i : I) (k : ℕ) (hk : k ≤ j) (y : Fin a → ℝ) (hy : y ∈ S i) :
      ell^k*‖iteratedFDeriv ℝ k (f i) y‖ ≤ C := by
    obtain ⟨b,hyb⟩ := hCover i y hy
    have hc := actual_fast_joint_chart_transfer T hT k (phi i b) (g i b) (U i b) (O i b)
      (hU i b) (hO i b) (hphi i b) (hg i b) (hMap i b) y hyb ell ell K hell le_rfl
      (fun l hl => hJets i b l (hl.trans hk) y ⟨hy,hyb⟩)
      (fun l hl hlk => hTransition i b l hl (hlk.trans hk) y ⟨hy,hyb⟩)
    have hc' : ell^k*‖iteratedFDeriv ℝ k (g i b ∘ phi i b) y‖ ≤
        actualFastChartTransferPrefix T j*K := hc.trans
      (mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix T hT hk) hK)
    have hl := slow_linear_jet_bound cy (U i b) (hU i b) (g i b ∘ phi i b)
      ((hg i b).comp (hphi i b) (hMap i b)) k ell (actualFastChartTransferPrefix T j*K)
      hell.le y hyb hc'
    have heq := eventuallyEq_of_mem ((hU i b).mem_nhds hyb) (fun z hz => hEq i b hz)
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hl.trans_eq (by dsimp only [C]; ring)
  have hout := parameterRound2_paperAtlasWeighted_le_of_weighted_jets j ell C hell hell1 hC
    f V S hV hSV hf hb
  have hr := actual_paperAtlasWeighted_open_restrict 0 j ell f D V S hD hV hVD hSV
  refine ⟨hf,?_⟩
  rw [hr]
  exact hout

#print axioms round3_original_weighted_norm_from_native_open_cover
end GlobalEmbedding.Continuation
