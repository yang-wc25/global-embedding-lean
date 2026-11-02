import Initialization.Colored.SelectorReferenceJets
import Initialization.Assembly.SelectorSecondChain

/-!
# Uniform reference jets for genuine sphere-source pullbacks

The ambient inclusion is the actual inclusion of the given native sphere map.
Both the selected map and the outer derivative field have fixed-order bounds
chosen from the fixed selector before any sphere argument, frequency, or chart.
This includes the chart-local setting, with no extension of chart support claims.
-/

noncomputable section
open Function Set Metric
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} (C : Fin n → ℕ) [∀ i, Fact (0 < C i)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The true outer derivative evaluated on the actual native sphere argument. -/
def selectorSourceOuterDerivative (S : FreeHopfProduct C → F)
    (z : E → FreeHopfProduct C) (x : E) : HopfProductAmbient C →L[ℝ] F :=
  fderiv ℝ (selectorAmbientExtension C S) (selectorSourceAmbient C z x)

theorem selectorSourceOuterDerivative_contDiffOn
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct C) (O : Set E) (hO : IsOpen O)
    (hZ : ContDiffOn ℝ ∞ (selectorSourceAmbient C z) O) :
    ContDiffOn ℝ ∞ (selectorSourceOuterDerivative C S z) O := by
  have hg : ContDiffOn ℝ ∞ (selectorAmbientExtension C S) (hopfRadialDomain C) :=
    fun y hy ↦ (selectorAmbientExtension_contDiffAt C S hS hy).contDiffWithinAt
  exact (hg.fderiv_of_isOpen (hopfRadialDomain C).isOpen
    (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))).comp hZ
      (fun y _ ↦ hopfProductInclusion_mem_radial C (z y))

/-- A direct actual-composition bound on the native selected map. -/
theorem selectorSource_reference_jet_bound
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct C) (O : Set E) (hO : IsOpen O)
    (hZ : ContDiffOn ℝ ∞ (selectorSourceAmbient C z) O)
    (x : E) (hx : x ∈ O) (j : ℕ) (B D : ℝ)
    (houter : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (selectorAmbientExtension C S)
      (selectorSourceAmbient C z x)‖ ≤ B)
    (hinner : ∀ i, 1 ≤ i → i ≤ j →
      ‖iteratedFDeriv ℝ i (selectorSourceAmbient C z) x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ j (S ∘ z) x‖ ≤ (j.factorial : ℝ) * B * D ^ j := by
  have hg : ContDiffOn ℝ ∞ (selectorAmbientExtension C S) (hopfRadialDomain C) :=
    fun y hy ↦ (selectorAmbientExtension_contDiffAt C S hS hy).contDiffWithinAt
  have hmaps : MapsTo (selectorSourceAmbient C z) O (hopfRadialDomain C) :=
    fun y _ ↦ hopfProductInclusion_mem_radial C (z y)
  have houter' (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i (selectorAmbientExtension C S) (hopfRadialDomain C)
        (selectorSourceAmbient C z x)‖ ≤ B := by
    rw [iteratedFDerivWithin_of_isOpen i (hopfRadialDomain C).isOpen (hmaps hx)]
    exact houter i hi
  have hinner' (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i (selectorSourceAmbient C z) O x‖ ≤ D ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hO hx]
    exact hinner i hi hij
  have hb := norm_iteratedFDerivWithin_comp_le hg hZ
    (by simp : (j : ℕ∞ω) ≤ ∞) (hopfRadialDomain C).isOpen.uniqueDiffOn
    hO.uniqueDiffOn hmaps hx houter' hinner'
  have heq : selectorAmbientExtension C S ∘ selectorSourceAmbient C z = S ∘ z := by
    funext y
    exact selectorAmbientExtension_inclusion C S (z y)
  rwa [iteratedFDerivWithin_of_isOpen j hO hx, heq] at hb

/-- The actual derivative field of the selector has the same composition bound,
using one more actual ambient derivative of the already fixed selector. -/
theorem selectorSourceOuterDerivative_reference_jet_bound
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct C) (O : Set E) (hO : IsOpen O)
    (hZ : ContDiffOn ℝ ∞ (selectorSourceAmbient C z) O)
    (x : E) (hx : x ∈ O) (j : ℕ) (B D : ℝ)
    (houter : ∀ i ≤ j, ‖iteratedFDeriv ℝ (i+1) (selectorAmbientExtension C S)
      (selectorSourceAmbient C z x)‖ ≤ B)
    (hinner : ∀ i, 1 ≤ i → i ≤ j →
      ‖iteratedFDeriv ℝ i (selectorSourceAmbient C z) x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ j (selectorSourceOuterDerivative C S z) x‖ ≤
      (j.factorial : ℝ) * B * D ^ j := by
  have hg : ContDiffOn ℝ ∞ (selectorAmbientExtension C S) (hopfRadialDomain C) :=
    fun y hy ↦ (selectorAmbientExtension_contDiffAt C S hS hy).contDiffWithinAt
  have hdf := hg.fderiv_of_isOpen (hopfRadialDomain C).isOpen
    (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))
  have hmaps : MapsTo (selectorSourceAmbient C z) O (hopfRadialDomain C) :=
    fun y _ ↦ hopfProductInclusion_mem_radial C (z y)
  have houter' (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i (fderiv ℝ (selectorAmbientExtension C S))
        (hopfRadialDomain C) (selectorSourceAmbient C z x)‖ ≤ B := by
    rw [iteratedFDerivWithin_of_isOpen i (hopfRadialDomain C).isOpen (hmaps hx),
      norm_iteratedFDeriv_fderiv]
    exact houter i hi
  have hinner' (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i (selectorSourceAmbient C z) O x‖ ≤ D ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hO hx]
    exact hinner i hi hij
  have hb := norm_iteratedFDerivWithin_comp_le hdf hZ
    (by simp : (j : ℕ∞ω) ≤ ∞) (hopfRadialDomain C).isOpen.uniqueDiffOn
    hO.uniqueDiffOn hmaps hx houter' hinner'
  rwa [iteratedFDerivWithin_of_isOpen j hO hx] at hb

/-- Both reference sequences are fixed from the same selector and a prepared
inner-jet budget before the actual sphere map and all later parameters. -/
theorem exists_selectorSource_reference_bounds
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S) (U : ℕ → ℝ) :
    ∃ R : ℕ → ℝ, (∀ j, 0 < R j) ∧
      ∀ (z : E → FreeHopfProduct C) (O : Set E) (hO : IsOpen O)
        (hZ : ContDiffOn ℝ ∞ (selectorSourceAmbient C z) O)
        (x : E) (hx : x ∈ O) (j : ℕ),
        (∀ i, 1 ≤ i → i ≤ j →
          ‖iteratedFDeriv ℝ i (selectorSourceAmbient C z) x‖ ≤ U j) →
        ‖iteratedFDeriv ℝ j (S ∘ z) x‖ ≤ R j ∧
        ‖iteratedFDeriv ℝ j (selectorSourceOuterDerivative C S z) x‖ ≤ R j := by
  obtain ⟨B, hBpos, hB⟩ := selectorAmbientExtension_uniform_derivatives C S hS
  let R : ℕ → ℝ := fun j ↦ max 1 ((j.factorial : ℝ) *
    coloredSelectorOuterEnvelope B (j+1) * (max 1 (U j)) ^ j)
  refine ⟨R, fun j ↦ lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z O hO hZ x hx j hj
  have hin (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDeriv ℝ i (selectorSourceAmbient C z) x‖ ≤ (max 1 (U j)) ^ i :=
    (hj i hi hij).trans ((le_max_right _ _).trans
      (le_self_pow₀ (le_max_left _ _) (by omega)))
  have hout (i : ℕ) (hi : i ≤ j+1) :
      ‖iteratedFDeriv ℝ i (selectorAmbientExtension C S) (selectorSourceAmbient C z x)‖ ≤
        coloredSelectorOuterEnvelope B (j+1) :=
    (hB i (z x)).trans
      (le_coloredSelectorOuterEnvelope B (fun k ↦ (hBpos k).le) hi)
  constructor
  · exact (selectorSource_reference_jet_bound C S hS z O hO hZ x hx j _ _
      (fun i hi ↦ hout i (by omega)) hin).trans (le_max_right _ _)
  · exact (selectorSourceOuterDerivative_reference_jet_bound C S hS z O hO hZ x hx j _ _
      (fun i hi ↦ hout (i+1) (by omega)) hin).trans (le_max_right _ _)

end GlobalEmbedding.Initialization
