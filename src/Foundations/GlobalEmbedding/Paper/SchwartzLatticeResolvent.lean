import GlobalEmbedding.Paper.SchwartzLatticeLaplacian
import GlobalEmbedding.External.OpenAIMath.Analysis.SchwartzShiftedLaplacian

open scoped SchwartzMap Laplacian ContDiff

namespace GlobalEmbedding.Paper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Periodize an actual entire-space Schwartz shifted resolvent. The resulting function
is genuinely smooth and lattice-periodic and solves (1−Δ)u=periodization(f). Arbitrary
periodic forcing is not assumed Schwartz: a separate compact partition is needed to
represent it as periodization(f). The construction includes dimension zero. -/
theorem exists_smooth_lattice_periodic_resolvent
    (L : Submodule ℤ E) [DiscreteTopology L] (f : 𝓢(E, ℝ)) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧
      (∀ (z : L) (x : E), u (x + z) = u x) ∧
      ∀ x, u x - Laplacian.laplacian u x = schwartzLatticePeriodization L f x := by
  obtain ⟨v, he⟩ :=
    GlobalEmbedding.External.OpenAIMath.SchwartzShiftedLaplacian.exists_real_schwartz_resolvent f
  have hr := schwartz_lattice_periodization_regular L v
  refine ⟨schwartzLatticePeriodization L v, hr.1, hr.2.2, fun x => ?_⟩
  let b := stdOrthonormalBasis ℝ E
  let T : (E [×2]→L[ℝ] ℝ) →L[ℝ] ℝ := ∑ i,
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![b i, b i]
  have ht (y : E) : T (iteratedFDeriv ℝ 2 v y) = Laplacian.laplacian (v : E → ℝ) y := by
    simp only [T, sum_apply, ContinuousMultilinearMap.apply_apply,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, b]
  obtain ⟨v₀, hv₀, hb₀⟩ := schwartz_lattice_jet_majorant L v 0 (norm_nonneg x)
  have hs₀ : Summable (fun z : L => v (x + z)) :=
    Summable.of_norm_bounded hv₀ (fun z => by simpa using hb₀ z x le_rfl)
  obtain ⟨v₂, hv₂, hb₂⟩ := schwartz_lattice_jet_majorant L v 2 (norm_nonneg x)
  have hs₂ : Summable (fun z : L => Laplacian.laplacian (v : E → ℝ) (x + z)) := by
    have h := T.summable (Summable.of_norm_bounded hv₂ (fun z => hb₂ z x le_rfl))
    exact h.congr (fun z => ht (x + z))
  rw [schwartz_lattice_periodization_laplacian, schwartzLatticePeriodization,
    ← Summable.tsum_sub hs₀ hs₂]
  exact tsum_congr (fun z => by simpa only [one_mul] using he (x + z))

#print axioms exists_smooth_lattice_periodic_resolvent

end GlobalEmbedding.Paper
