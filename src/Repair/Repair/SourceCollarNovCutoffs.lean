import Repair.SourceCollarNovFiniteCover
import Smoothing.TensorTransferJets

/-!
# Actual smooth cutoff pieces on the original source collars

The pieces are the original cutoff multiplied by the constructed square
partition in its original coordinate chart. They extend by zero through that
same chart. Their square sum is the original cutoff squared at every point.
Their supports are contained in the original cutoff support, so an overlap
can only occur on an original overlap. All original-coordinate derivatives
are those of the literal product, with an explicit fixed all-order budget.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Filter Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M]

/-- The literal original-chart zero extension. -/
def sourceCollarNovCutoff (e : OpenPartialHomeomorph M E)
    (theta : M → ℝ) (eta : E → ℝ) : M → ℝ :=
  e.source.indicator (fun x => theta x * eta (e x))

theorem sourceCollarNovCutoff_tsupport_original (e : OpenPartialHomeomorph M E)
    (theta : M → ℝ) (eta : E → ℝ) :
    tsupport (sourceCollarNovCutoff e theta eta) ⊆ tsupport theta := by
  apply closure_minimal _ (isClosed_tsupport theta)
  intro x hx
  apply subset_tsupport
  intro hzero
  apply hx
  simp [sourceCollarNovCutoff, Set.indicator_apply, hzero]

theorem sourceCollarNovCutoff_tsupport (e : OpenPartialHomeomorph M E)
    (theta : M → ℝ) (eta : E → ℝ) (hTheta : tsupport theta ⊆ e.source) :
    tsupport (sourceCollarNovCutoff e theta eta) ⊆
      tsupport theta ∩ (e.source ∩ e ⁻¹' tsupport eta) := by
  intro x hx
  have hxt := sourceCollarNovCutoff_tsupport_original e theta eta hx
  have hxs := hTheta hxt
  refine ⟨hxt, hxs, ?_⟩
  by_contra hn
  have hc := e.continuousOn.continuousAt (e.open_source.mem_nhds hxs)
  have hezero := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto hc
  have hfzero : sourceCollarNovCutoff e theta eta =ᶠ[𝓝 x] 0 := by
    filter_upwards [hezero] with y hy
    simp [sourceCollarNovCutoff, Set.indicator_apply, show eta (e y) = 0 from hy]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hfzero) hx

variable [ChartedSpace E M]

theorem sourceCollarNovCutoff_contMDiff (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    (theta : M → ℝ) (eta : E → ℝ)
    (hTheta : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ theta)
    (hSupport : tsupport theta ⊆ e.source) (hEta : ContDiff ℝ ∞ eta) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (sourceCollarNovCutoff e theta eta) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxs := hSupport (sourceCollarNovCutoff_tsupport_original e theta eta hx)
  have hs := hTheta.contMDiffAt.mul
    (hEta.contMDiff.contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas he hxs))
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hxs] with y hy
  exact Set.indicator_of_mem hy _

omit [ChartedSpace E M] in
theorem sourceCollarNovCutoff_original_jets (e : OpenPartialHomeomorph M E)
    (theta : M → ℝ) (eta : E → ℝ) (j : ℕ) (y : E) (hy : y ∈ e.target) :
    iteratedFDeriv ℝ j (sourceCollarNovCutoff e theta eta ∘ e.symm) y =
      iteratedFDeriv ℝ j (fun z => theta (e.symm z) * eta z) y := by
  have hEq : sourceCollarNovCutoff e theta eta ∘ e.symm =ᶠ[𝓝 y]
      (fun z => theta (e.symm z) * eta z) := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    simp only [Function.comp_apply, sourceCollarNovCutoff,
      Set.indicator_of_mem (e.map_target hz), e.right_inv hz]
  exact (hEq.iteratedFDeriv ℝ j).eq_of_nhds

variable {A : BufferedAtlas M E} {Omega : Fin A.count → Set E} {R b : ℝ} {hb : 0 < b}

def SourceCollarNovFamily.cutoff (s : SourceCollarNovFamily A Omega R b hb)
    (theta : Fin A.count → M → ℝ) (i : Fin A.count) (c : s.centers i) : M → ℝ :=
  sourceCollarNovCutoff (A.chart i) (theta i)
    (round4RefinementSquareCutoff E (s.centers i) (b / 8) c)

theorem SourceCollarNovFamily.cutoff_tsupport
    (s : SourceCollarNovFamily A Omega R b hb)
    (theta : Fin A.count → M → ℝ)
    (hTheta : ∀ i, tsupport (theta i) ⊆ A.inner i)
    (i : Fin A.count) (c : s.centers i) :
    tsupport (s.cutoff theta i c) ⊆ tsupport (theta i) ∩
      ((A.chart i).source ∩ (A.chart i) ⁻¹' s.carrier i c) := by
  have h := sourceCollarNovCutoff_tsupport (A.chart i) (theta i)
    (round4RefinementSquareCutoff E (s.centers i) (b / 8) c)
    ((hTheta i).trans (A.inner_subset i))
  have hNative := (round4_refinement_square_cutoffs E (s.centers i) (b / 8)
    (by positivity) (s.separated i)).2.1 c
  intro x hx
  have hh := h hx
  refine ⟨hh.1, hh.2.1, ?_⟩
  change A.chart i x ∈ closedBall c.val (b / 4)
  have hr : 2 * (b / 8) = b / 4 := by ring
  simpa only [hr] using hNative hh.2.2

theorem SourceCollarNovFamily.cutoff_square_sum
    (s : SourceCollarNovFamily A Omega R b hb)
    (theta : Fin A.count → M → ℝ)
    (hTheta : ∀ i, tsupport (theta i) ⊆ A.inner i)
    (i : Fin A.count) (x : M) :
    (∑ c : s.centers i, s.cutoff theta i c x ^ 2) = theta i x ^ 2 := by
  classical
  by_cases hx : theta i x = 0
  · simp [SourceCollarNovFamily.cutoff, sourceCollarNovCutoff, Set.indicator_apply, hx]
  · have hxi := hTheta i (subset_tsupport (theta i) hx)
    have hxs := A.inner_subset i hxi
    obtain ⟨W, hWopen, hWin, hWsum⟩ := round4_refinement_square_partition_near E
      (s.centers i) (b / 8) (by positivity) (bufferedInnerCoordinates A i) (s.covers i)
    have hsum := hWsum (A.chart i x) (hWin (bufferedInnerCoordinates_mem A i hxi))
    simp only [SourceCollarNovFamily.cutoff, sourceCollarNovCutoff,
      Set.indicator_of_mem hxs, mul_pow]
    rw [← Finset.mul_sum, hsum, mul_one]

theorem SourceCollarNovFamily.cutoff_contMDiff [IsManifold 𝓘(ℝ,E) ∞ M]
    (s : SourceCollarNovFamily A Omega R b hb) (hA : IsSmoothBufferedAtlas A)
    (theta : Fin A.count → M → ℝ)
    (hTheta : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆ A.inner i)
    (i : Fin A.count) (c : s.centers i) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s.cutoff theta i c) :=
  sourceCollarNovCutoff_contMDiff (A.chart i) (hA.chart_mem i) (theta i) _
    (hTheta i) ((hSupport i).trans (A.inner_subset i))
    ((round4_refinement_square_cutoffs E (s.centers i) (b / 8)
      (by positivity) (s.separated i)).1 c)

theorem SourceCollarNovFamily.cutoff_original_jet_bound
    (s : SourceCollarNovFamily A Omega R b hb)
    (theta : Fin A.count → M → ℝ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hSmooth : ∀ i, ContDiffOn ℝ ∞ (theta i ∘ (A.chart i).symm) (A.chart i).target)
    (hSampling : ∀ i, Omega i ⊆ (A.chart i).target)
    (hJets : ∀ i j y, y ∈ Omega i →
      ‖iteratedFDeriv ℝ j (theta i ∘ (A.chart i).symm) y‖ ≤ B j)
    (i : Fin A.count) (c : s.centers i) (j : ℕ) (y : E) (hy : y ∈ Omega i) :
    ‖iteratedFDeriv ℝ j (s.cutoff theta i c ∘ (A.chart i).symm) y‖ ≤
      tensorProductJetConstant B (round4RefinementSquareProfile E (b / 8) (by positivity)) j := by
  rw [SourceCollarNovFamily.cutoff, sourceCollarNovCutoff_original_jets _ _ _ j y (hSampling i hy)]
  apply tensor_scalar_product_jet_le B _ hB
    (round4RefinementSquareProfile_nonneg E (b / 8) (by positivity))
    (A.chart i).open_target (hSmooth i)
    (((round4_refinement_square_cutoffs E (s.centers i) (b / 8)
      (by positivity) (s.separated i)).1 c).contDiffOn) (hSampling i hy) j
  · intro k
    exact hJets i k y hy
  · intro k
    exact (round4_refinement_square_cutoffs E (s.centers i) (b / 8)
      (by positivity) (s.separated i)).2.2.2 c k y

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.SourceCollarNovFamily.cutoff_square_sum
#print axioms GlobalEmbedding.Continuation.SourceCollarNovFamily.cutoff_original_jet_bound
