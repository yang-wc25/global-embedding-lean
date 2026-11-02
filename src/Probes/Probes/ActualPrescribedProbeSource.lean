import Probes.ActualSourceRestriction

/-!
# Primitive source for the prescribed paired normal probe

The dictionary is built from the literal -(delta*tau)/lambda² chi nu section
in the original normal bundle. Its source is the original h=0 mode source,
with cosine/sine columns s and -i*s. Primitive joint jets of true B, chi and
nu supply every source-only jet required by the same finite solver.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Manifold Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Offline

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m + 1) → ℂ

/-- The SAME actual source dictionary used by the first-block reconstruction. -/
def actualPrescribedProbeSource
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (delta tau lam : ℝ) (b : Ep) : Fin p → D → Cdata :=
  pairedProbeSourceDictionary label l (fun x ↦ actualHomogeneousSource F hF chart
    (actualProbeNormalAmplitude F chart chi nu delta tau lam) (b, x))

/-- Exact source identity for (8.3), including its negative imaginary sine
amplitude. This identifies the input to the original finite solver itself. -/
theorem finiteProbeSource_actualPrescribedProbeSource
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (delta tau lam : ℝ) (b : Ep) (u : Fin p → ℝ) :
    finiteProbeSource (actualPrescribedProbeSource label l F hF chart chi nu delta tau lam b) u =
      actualPairedNormalSource label l (F b) (hF b) (chart b)
        (actualProbeNormalAmplitude F chart chi nu delta tau lam b) u := by
  exact (actualPairedNormalSource_eq_finite_source label l (F b) (hF b) (chart b)
    (actualProbeNormalAmplitude F chart chi nu delta tau lam b) u).symm

/-- Primitive actual geometric profiles give the spatial source-column
budgets required by all full-family jet bounds. No reconstructed-wave or
source bound is supplied as a hypothesis. The constant is unchanged by
freezing the auxiliary parameter and by the actual -i sine channel. -/
theorem actualPrescribedProbeSource_weighted_jets
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (O : Set X) (hO : IsOpen O)
    (hB : ContDiffOn ℝ ∞ (fun z : X ↦ fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)) O)
    (hchi : ContDiffOn ℝ ∞ chi O)
    (hnu : ContDiffOn ℝ ∞ (fun z : X ↦ (nu z.1 z.2 : V)) O)
    (j : ℕ) (ell delta tau lam MB Bchi Bnu : ℝ)
    (hell : 0 ≤ ell) (hdelta : 0 ≤ delta) (htau : 0 ≤ tau)
    (hMB : 0 ≤ MB) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hBb : ∀ k ≤ j, ∀ z ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k
      (fun y : X ↦ fun i : Fin (m + 1) ↦
        (incrementsModeSecondForm (F y.1) (hF y.1) (chart y.1) y.2 0 i : V)) z‖ ≤ MB)
    (hchib : ∀ k ≤ j, ∀ z ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (hnub : ∀ k ≤ j, ∀ z ∈ O, ell ^ k *
      ‖iteratedFDeriv ℝ k (fun y : X ↦ (nu y.1 y.2 : V)) z‖ ≤ Bnu) (b : Ep) :
    let C := homogeneousSourceConstant m N j MB (probeNormalAmplitudeConstant j lam Bchi Bnu)
    (∀ q, ContDiffOn ℝ ∞
      (actualPrescribedProbeSource label l F hF chart chi nu delta tau lam b q)
      ((fun x ↦ (b, x)) ⁻¹' O)) ∧
    ∀ q n, n ≤ j → ∀ x, (b, x) ∈ O → ell ^ n * ‖iteratedFDeriv ℝ n
      (actualPrescribedProbeSource label l F hF chart chi nu delta tau lam b q) x‖ ≤ C * (delta * tau) := by
  dsimp only
  let s := actualHomogeneousSource F hF chart (actualProbeNormalAmplitude F chart chi nu delta tau lam)
  let C := homogeneousSourceConstant m N j MB (probeNormalAmplitudeConstant j lam Bchi Bnu)
  have hs := actualProbeHomogeneousSource_weighted_jets F hF chart chi nu O hO hB hchi hnu
    j ell delta tau lam MB Bchi Bnu hell hdelta htau hMB hBchi hBnu hBb hchib hnub
  have ht := fixed_parameter_slice_weighted_jets s O hO hs.1 j ell (C * (delta * tau)) hell hs.2 b
  have hC : 0 ≤ C := homogeneousSourceConstant_nonneg m N j hMB
    (probeNormalAmplitudeConstant_nonneg j lam hBchi hBnu)
  refine ⟨fun q ↦ pairedProbeSourceDictionary_contDiffOn label l _ _ ht.1 q, ?_⟩
  intro q n hn x hx
  apply pairedProbeSourceDictionary_weighted_jet_bound label l (fun y ↦ s (b, y)) n x
    ((ht.1.contDiffAt ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hx)).of_le (by simp))
    ell (C * (delta * tau)) (mul_nonneg hC (mul_nonneg hdelta htau)) (ht.2 n hn x hx) q

#print axioms finiteProbeSource_actualPrescribedProbeSource
#print axioms actualPrescribedProbeSource_weighted_jets
end GlobalEmbedding.Offline
