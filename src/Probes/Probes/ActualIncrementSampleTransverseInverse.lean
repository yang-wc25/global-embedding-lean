import Probes.ActualOriginalTransverseInverse
import Probes.ActualIncrementSampleGram

/-! The same canonical included J is smooth on its genuine injectivity
locus and has the original quantitative profile only on the original samples. -/
noncomputable section
open GlobalEmbedding.Paper Manifold Set
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "P" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ P
local notation "X" => Ep × D

theorem actual_original_transverse_J_on_samples
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (chart : Ep → D → M) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (chart z.1) z.2) O)
    (hinj : ∀ z ∈ O, Function.Injective (incrementsModeAmbientTransverseFrame
      (F z.1) (hF z.1) (chart z.1) z.2))
    (j : ℕ) (ell c MA : ℝ) (hell : 0 < ell) (hc : 0 < c) (hMA : 0 ≤ MA)
    (hreserve : ∀ z ∈ S, ∀ v : Tdata, c * ‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (chart z.1) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => incrementsModeAmbientTransverseFrame (F y.1) (hF y.1) (chart y.1) y.2) z‖ ≤ MA) :
    let J := fun z : X => (normalSpace (I := I) (F z.1) (chart z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (chart z.1) z.2)
    ContDiffOn ℝ ∞ J O ∧
    ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k J z‖ ≤
      2^j * MA * slowInverseMajorant c⁻¹ (2^j * MA^2) j := by
  dsimp only
  let A : X → Tdata →L[ℝ] V := fun z =>
    incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (chart z.1) z.2
  have he : (fun z : X => (normalSpace (I := I) (F z.1) (chart z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (chart z.1) z.2)) =
        fun z => freeGramRightInverse (A z) := by
    funext z
    exact incrementsModeCoordinateJ_ambient (F z.1) (hF z.1) (chart z.1) z.2
  rw [he]
  exact actual_freeGramRightInverse_slow_jets_on_samples A O S hO hSO hA hinj j ell c MA hell hc hMA hreserve hAj

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_transverse_J_on_samples
