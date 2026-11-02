import Initialization.Colored.SphereMap

/-!
# Smooth zero extension and the actual whole-product colored map

The phases need only be smooth on the cutoff's topological support. They may
be arbitrary elsewhere. The weighted terms extend smoothly by zero because
they vanish on a neighborhood of each point outside that support.
-/

noncomputable section

open Function Set Metric Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization

open GlobalEmbedding.Paper

variable {ι E H M : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The actual real-frequency period-one complex phase is globally smooth. -/
theorem coloredExponential_contDiff (T : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ (Circle.exp (2 * Real.pi * T * t) : ℂ)) := by
  change ContDiff ℝ ∞ (fun t : ℝ ↦ Complex.exp ((2 * Real.pi * T * t : ℝ) * Complex.I))
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
    contDiff_const).cexp

/-- Multiplication by the actual cutoff makes the supported local phase smooth
on the entire source. This includes every support boundary point. -/
theorem coloredWave_contMDiff (χ ℓ : M → ℝ) (T : ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hℓ : ∀ x ∈ tsupport χ, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ℓ x) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (coloredWave χ ℓ T) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxχ : x ∈ tsupport χ := tsupport_smul_subset_left _ _ hx
  exact (hχ x).smul
    ((coloredExponential_contDiff T).contMDiff.contMDiffAt.comp x (hℓ x hxχ))

/-- Each literal color sum in (7.2) is globally smooth. No global regularity
is requested from the unsupported coordinate functions. -/
theorem coloredCoordinate_contMDiff {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → M → ℝ) (T : ℝ)
    (hχ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ i))
    (hℓ : ∀ i x, x ∈ tsupport (χ i) → ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (ℓ i) x)
    (c : Fin C) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (coloredCoordinate color χ ℓ T c) := by
  classical
  apply ContMDiff.sum
  intro i _
  by_cases hic : color i = c
  · simpa only [hic, ite_true] using coloredWave_contMDiff (χ i) (ℓ i) T (hχ i) (hℓ i)
  · simpa only [hic, ite_false] using
      (contMDiff_const : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun _ : M ↦ (0 : ℂ)))

/-- The actual finite complex Euclidean map is smooth in the original native
L² ambient space, rather than merely in a function-space replacement. -/
theorem coloredAmbient_contMDiff {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → M → ℝ) (T : ℝ)
    (hχ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ i))
    (hℓ : ∀ i x, x ∈ tsupport (χ i) → ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (ℓ i) x) :
    ContMDiff I 𝓘(ℝ, PlanarHopfAmbient C) ∞ (coloredAmbient color χ ℓ T) := by
  have hp : ContMDiff I 𝓘(ℝ, Fin C → ℂ) ∞
      (fun x c ↦ coloredCoordinate color χ ℓ T c x) :=
    contMDiff_pi_module_iff.mpr
      (fun c ↦ coloredCoordinate_contMDiff color χ ℓ T hχ hℓ c)
  exact PiLp.contDiff_toLp.contMDiff.comp hp

/-- Smoothness into the genuine native Hopf sphere follows from its actual
ambient map and the already proved exact unit-norm identity. -/
theorem coloredSphere_contMDiff {C : ℕ} [Fact (0 < C)] (color : ι → Fin C)
    (χ ℓ : ι → M → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ)
    (hχ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ i))
    (hℓ : ∀ i x, x ∈ tsupport (χ i) → ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (ℓ i) x) :
    ContMDiff I (planarHopfModel C) ∞ (coloredSphere color χ ℓ hdisjoint hsquare T) :=
  (coloredAmbient_contMDiff color χ ℓ T hχ hℓ).codRestrict_sphere
    (coloredAmbient_mem_sphere color χ ℓ hdisjoint hsquare T)

/-- The literal whole-product sphere argument of the one fixed selector. -/
def coloredProduct {n C : ℕ} (color : ι → Fin C) (χ : ι → M → ℝ)
    (ℓ : Fin n → ι → M → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ) (x : M) :
    FreeHopfProduct (fun _ : Fin n ↦ C) :=
  fun l ↦ coloredSphere color χ (ℓ l) hdisjoint hsquare T x

/-- All factors are assembled using the actual native product manifold atlas. -/
theorem coloredProduct_contMDiff {n C : ℕ} [Fact (0 < C)]
    (color : ι → Fin C) (χ : ι → M → ℝ) (ℓ : Fin n → ι → M → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ)
    (hχ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ i))
    (hℓ : ∀ l i x, x ∈ tsupport (χ i) →
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (ℓ l i) x) :
    ContMDiff I (freeHopfModel (fun _ : Fin n ↦ C)) ∞
      (coloredProduct color χ ℓ hdisjoint hsquare T) := by
  rw [show freeHopfModel (fun _ : Fin n ↦ C) =
    ModelWithCorners.pi (fun _ : Fin n ↦ planarHopfModel C) from
      (free_finite_product_model_eq _).symm]
  apply contMDiff_pi_iff.mpr
  intro l
  exact coloredSphere_contMDiff color χ (ℓ l) hdisjoint hsquare T hχ (hℓ l)

/-- The map in (7.2), using the one chosen whole-product selector literally. -/
def coloredSelectorMap {n C : ℕ} {F : Type*}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (color : ι → Fin C) (χ : ι → M → ℝ) (ℓ : Fin n → ι → M → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ) : M → F :=
  S ∘ coloredProduct color χ ℓ hdisjoint hsquare T

/-- The same actual selector composition is smooth on the entire source. -/
theorem coloredSelectorMap_contMDiff {n C : ℕ} [Fact (0 < C)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ C)) 𝓘(ℝ, F) ∞ S)
    (color : ι → Fin C) (χ : ι → M → ℝ) (ℓ : Fin n → ι → M → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ)
    (hχ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ i))
    (hℓ : ∀ l i x, x ∈ tsupport (χ i) →
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (ℓ l i) x) :
    ContMDiff I 𝓘(ℝ, F) ∞ (coloredSelectorMap S color χ ℓ hdisjoint hsquare T) :=
  hS.comp (coloredProduct_contMDiff color χ ℓ hdisjoint hsquare T hχ hℓ)

/-- Compactness of the fixed selector's whole domain bounds the SAME map
uniformly before the frequency, cutoff family or local phase choices. -/
theorem exists_coloredSelectorMap_value_bound {n C : ℕ} [Fact (0 < C)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F) (hS : Continuous S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (color : ι → Fin C) (χ : ι → M → ℝ)
      (ℓ : Fin n → ι → M → ℝ)
      (hdisjoint : ∀ i j, i ≠ j → color i = color j →
        Disjoint (tsupport (χ i)) (tsupport (χ j)))
      (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ) (x : M),
      ‖coloredSelectorMap S color χ ℓ hdisjoint hsquare T x‖ ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image hS.norm.continuousOn
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro color χ ℓ hdisjoint hsquare T x
  exact (hB (Set.mem_image_of_mem _ (Set.mem_univ _))).trans (le_max_right _ _)

end GlobalEmbedding.Initialization
