import AuxNormBridge.BufferedCore
import Smoothing.ParameterGeometryModel
import Smoothing.ParameterRound2CompactNorms
import Probes.Round3ParameterPrimaryChartSmooth

/-!
# All original coordinate jets are finite on unchanged norm domains

Compact cores are manufactured from the actual original buffer and radius.
An arbitrary smooth map has finite jets on those cores.  The original
transition bounds transport the jets to every point of every original norm
domain.  Those domains may be open or noncompact; they are not replaced by
compact domains.  The resulting high-order profile depends on the actual
smooth input and adds no high-order entrance condition.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold IsManifold Set Function Metric Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation.AuxNormBridge

variable {E F X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]

/-- A fixed-order bound on the original compact cores, uniform over the
finite original atlas and all lower derivatives.  The cores themselves
are constructed from the buffer; compactness is not an input supplier. -/
theorem original_core_jet_prefix_bound
    (A : BufferedAtlas X E) (centers : Fin A.count → E) (radius : ℝ)
    (hBound : ∀ i, (A.chart i) '' A.inner i ⊆ closedBall (centers i) radius)
    (f : X → F)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i).target)
    (j : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ i k, k ≤ j → ∀ y ∈ protectedInnerClosure A i,
      ‖iteratedFDeriv ℝ k (f ∘ (A.chart i).symm) y‖ ≤ R := by
  classical
  have hEach : ∀ a : Fin A.count × Fin (j+1), ∃ R : ℝ,
      ∀ y ∈ protectedInnerClosure A a.1,
        ‖iteratedFDeriv ℝ (a.2 : ℕ) (f ∘ (A.chart a.1).symm) y‖ ≤ R := by
    intro a
    obtain ⟨R,hR⟩ := parameterRound2_coordinate_jets_bounded_of_compact
      (f ∘ (A.chart a.1).symm) (A.chart a.1).target
      (protectedInnerClosure A a.1) (protectedInnerClosure A a.1)
      (A.chart a.1).open_target (protectedInnerClosure_isCompact A centers radius hBound a.1)
      Subset.rfl (protectedInnerClosure_subset_target A a.1) (hf a.1) a.2
    exact ⟨R,fun y hy => hR ⟨⟨y,hy⟩,rfl⟩⟩
  choose R hR using hEach
  obtain ⟨B,hB⟩ := (Set.finite_range R).bddAbove
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro i k hk y hy
  let a : Fin A.count × Fin (j+1) := (i,⟨k,by omega⟩)
  exact (hR a y hy).trans ((hB (mem_range_self a)).trans (le_max_right _ _))

/-- All orders of the same map are bounded on the literal original Omega.
Only original positive-order coordinate-transition estimates are used.
The pointwise choice of one covering inner chart has no chart-count factor. -/
theorem original_coordinate_jet_profile_exists
    (A : BufferedAtlas X E) (hA : IsSmoothBufferedAtlas A)
    (centers : Fin A.count → E) (radius : ℝ)
    (hBound : ∀ i, (A.chart i) '' A.inner i ⊆ closedBall (centers i) radius)
    (Omega : Fin A.count → Set E)
    (hTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ (i j : Fin A.count) (k : ℕ), 1 ≤ k →
      ∀ y ∈ Omega i, y ∈ ((A.chart i).symm.trans (A.chart j)).source →
        ‖iteratedFDeriv ℝ k ((A.chart i).symm.trans (A.chart j)) y‖ ≤ T k)
    (f : X → F)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i).target) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ i k y, y ∈ Omega i → ‖iteratedFDeriv ℝ k (f ∘ (A.chart i).symm) y‖ ≤ C k := by
  classical
  have hOrder : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i y, y ∈ Omega i → ‖iteratedFDeriv ℝ k (f ∘ (A.chart i).symm) y‖ ≤ C := by
    intro k
    obtain ⟨R,hR,hCore⟩ := original_core_jet_prefix_bound A centers radius hBound f hf k
    refine ⟨(k.factorial : ℝ) * R * bufferedTransitionPrefix T k ^ k,
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hR)
        (pow_nonneg ((by norm_num : (0:ℝ) ≤ 1).trans (one_le_bufferedTransitionPrefix hT k)) _),?_⟩
    intro i y hy
    let x := (A.chart i).symm y
    obtain ⟨j,hj⟩ := A.cover x
    let e := (A.chart i).symm.trans (A.chart j)
    have he : y ∈ e.source := ⟨hTarget i hy,A.inner_subset j hj⟩
    have hSmooth : ContDiffOn ℝ ∞ e e.source :=
      (round3Parameter_partial_trans_smooth (A.chart i).symm (A.chart j)
        (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))
        (contMDiffOn_of_mem_maximalAtlas (hA.chart_mem j))).contDiffOn
    have hEq : (f ∘ (A.chart i).symm) =ᶠ[𝓝 y] (f ∘ (A.chart j).symm) ∘ e := by
      filter_upwards [e.open_source.mem_nhds he] with z hz
      change f ((A.chart i).symm z) = f ((A.chart j).symm (A.chart j ((A.chart i).symm z)))
      have hzj : (A.chart i).symm z ∈ (A.chart j).source := hz.2
      rw [(A.chart j).left_inv hzj]
    rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
    apply parameter_general_composition_jet_le T hT e.open_source (A.chart j).open_target
      hSmooth (hf j) (fun z hz => (A.chart j).map_source
        (show (A.chart i).symm z ∈ (A.chart j).source from hz.2)) he k R
    · intro l hl
      exact hCore j l hl (e y) (mem_protectedInnerClosure A j x hj)
    · intro l hl _
      exact hTransition i j l hl y hy he
  choose C hC hBounds using hOrder
  exact ⟨C,hC,fun i k y hy => hBounds k i y hy⟩

end GlobalEmbedding.Continuation.AuxNormBridge

#print axioms GlobalEmbedding.Continuation.AuxNormBridge.original_core_jet_prefix_bound
#print axioms GlobalEmbedding.Continuation.AuxNormBridge.original_coordinate_jet_profile_exists
