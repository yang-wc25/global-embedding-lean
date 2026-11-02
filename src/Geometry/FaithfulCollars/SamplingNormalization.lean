import FaithfulCollars.FixedBallRaw
import GlobalEmbedding.Offline.CutoffChartTransfer

/-!
# Square normalization with the original support and sampling contract

The former `TensorRawCutoffPreparation.inner_support` premise is not used.
The actual fixed-ball raw functions are produced internally.  The only jet
input here is the original chart-transition budget from setup:uniform.
Both raw and normalized functions retain the original chart labels, and all
constants precede the atlas.  The output estimates hold on the unchanged
chart targets, so restriction to any original norm sampling domain is literal.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def originalBallCutoff (A : BufferedAtlas M E) (rho : ℝ) : Fin A.count → M → ℝ :=
  squareNormalizedCutoff (originalBallRaw A rho)

theorem originalBallCutoff_support (A : BufferedAtlas M E) (rho : ℝ) (i : Fin A.count) :
    tsupport (originalBallCutoff A rho i) ⊆ tsupport (originalBallRaw A rho i) :=
  squareNormalizedCutoff_tsupport_subset _ _

/-- Genuine simultaneous all-order estimates for the SAME normalized
partition, manufactured from fixed-ball geometry.  No raw or normalized
cutoff, square-sum estimate or mixed-chart cutoff estimate is an input. -/
theorem exists_uniform_originalBallCutoffs
    (rho : ℝ) (hrho : 0 < rho) (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (D : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (A : BufferedAtlas M E) (g : OriginalFixedBallGeometry A rho)
        (hA : IsSmoothBufferedAtlas A),
      A.supportDegree ≤ D →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (A.chart p).target,
        (A.chart p).symm y ∈ A.support i →
        ‖iteratedFDeriv ℝ j (A.chart i ∘ (A.chart p).symm) y‖ ≤ T j) →
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (originalBallCutoff A rho i)) ∧
      (∀ x, ∑ i, originalBallCutoff A rho i x ^ 2 = 1) ∧
      (∀ i, tsupport (originalBallCutoff A rho i) ⊆ A.support i) ∧
      (∀ i, MapsTo (A.chart i) (tsupport (originalBallCutoff A rho i))
        (bufferedSamplingCoordinates A i)) ∧
      (∀ x, (activeCutoffIndices (originalBallCutoff A rho) x).card ≤ D + 1) ∧
      (∀ p i j, ∀ y ∈ (A.chart p).target,
        ‖iteratedFDeriv ℝ j (originalBallCutoff A rho i ∘ (A.chart p).symm) y‖ ≤ C j) := by
  obtain ⟨B, hB, hrawJets⟩ := exists_uniform_originalBallRaw_jets (E := E) (M := M) rho hrho
  obtain ⟨Cown, hCown, hnormalize⟩ := exists_normalizedCutoff_bounds_from_chartProviders
    (E := E) (M := M) B T hB hT (D + 1)
  obtain ⟨C, hC, htransfer⟩ := exists_actualChart_cutoff_transfer_bounds
    (E := E) (M := M) Cown T hCown hT
  refine ⟨C, hC, ?_⟩
  intro A g hA hD htrans
  have hs (i : Fin A.count) : tsupport (originalBallRaw A rho i) ⊆ (A.chart i).source :=
    fun _ hx => ((originalBallRaw_compact_support g i).2 hx).1
  obtain ⟨hchi, hsum, _, hsub, hown⟩ := hnormalize (Fin A.count) 1 le_rfl
    (originalBallRaw A rho) (originalBallRaw_smooth g hA)
    (originalBallRaw_plateau_cover g) (originalBallRaw_local_count g D hD)
    A.chart hA.chart_mem hs
    (by simpa only [one_pow, mul_one] using hrawJets A)
    (fun p i j hj y hy hx => htrans p i j hj y hy (originalBallRaw_enlarged_support g i hx))
  refine ⟨hchi, hsum,
    fun i => (hsub i).trans (originalBallRaw_enlarged_support g i),
    fun i x hx => originalBallRaw_original_sampling g i (hsub i hx), ?_, ?_⟩
  · intro x
    apply squareNormalizedCutoff_card_le_enlarged_degree A.support (originalBallRaw A rho)
      (originalBallRaw_enlarged_support g) D _ x
    intro i
    classical
    change A.supportGraph.degree i ≤ D
    exact (Finset.le_sup (f := fun j => A.supportGraph.degree j) (Finset.mem_univ i)).trans hD
  · intro p i j y hy
    by_cases hx : (A.chart p).symm y ∈ tsupport (originalBallCutoff A rho i)
    · have hr := hsub i hx
      have his := hs i hr
      have h := htransfer 1 le_rfl (originalBallCutoff A rho i) (hchi i)
        (A.chart p) (A.chart i) (hA.chart_mem p) (hA.chart_mem i) y ⟨hy, his⟩
        (fun k => hown i k _ ((A.chart i).map_source his))
        (fun k hk => htrans p i k hk y hy (originalBallRaw_enlarged_support g i hr)) j
      simpa only [one_pow, mul_one] using h
    · rw [iteratedFDeriv_comp_eq_zero_off_tsupport _ _ _
        ((A.chart p).symm.continuousAt hy) hx j, norm_zero]
      exact hC j

/-- Sampling certificates transfer the literal cutoff values, without
shrinking or replacing the original norm domains. -/
theorem originalBallCutoff_in_original_norm_domain
    (A : BufferedAtlas M E) (rho : ℝ) (g : OriginalFixedBallGeometry A rho)
    (Omega : Fin A.count → Set E)
    (hOmega : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) (i : Fin A.count) :
    MapsTo (A.chart i) (tsupport (originalBallCutoff A rho i)) (Omega i) := by
  intro x hx
  exact hOmega i (originalBallRaw_original_sampling g i (originalBallCutoff_support A rho i hx))

end GlobalEmbedding.Continuation.FaithfulCollars
