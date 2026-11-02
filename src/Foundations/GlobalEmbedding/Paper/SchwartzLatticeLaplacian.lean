import GlobalEmbedding.Paper.SchwartzLatticePeriodization
import Mathlib.Analysis.InnerProductSpace.Laplacian

open scoped SchwartzMap Laplacian

namespace GlobalEmbedding.Paper

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The actual Euclidean Laplacian commutes with actual Schwartz lattice periodization.
Use the genuine second-jet identity and the continuous linear orthonormal trace map;
absolute convergence comes from the Schwartz jet majorant. No PDE or formal exchange
of divergent series is assumed. -/
theorem schwartz_lattice_periodization_laplacian
    (L : Submodule ℤ E) [DiscreteTopology L] (f : 𝓢(E, F)) (x : E) :
    Laplacian.laplacian (schwartzLatticePeriodization L f) x =
      ∑' z : L, Laplacian.laplacian (f : E → F) (x + z) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let T : (E [×2]→L[ℝ] F) →L[ℝ] F := ∑ i,
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) F ![b i, b i]
  have ht (g : E → F) (y : E) :
      T (iteratedFDeriv ℝ 2 g y) = Laplacian.laplacian g y := by
    simp only [T, sum_apply, ContinuousMultilinearMap.apply_apply,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, b]
  obtain ⟨v, hv, hb⟩ := schwartz_lattice_jet_majorant L f 2 (norm_nonneg x)
  have hs : Summable (fun z : L => iteratedFDeriv ℝ 2 f (x + z)) :=
    Summable.of_norm_bounded hv (fun z => hb z x le_rfl)
  rw [← ht, (schwartz_lattice_periodization_regular L f).2.1 2 x, T.map_tsum hs]
  exact tsum_congr (fun z => ht (f : E → F) (x + z))

#print axioms schwartz_lattice_periodization_laplacian

end GlobalEmbedding.Paper
