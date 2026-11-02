import GlobalEmbedding.Paper.FreeHopfProductNative
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# A genuine ambient extension of a whole-product selector

Source: Proposition `prop:initialization`, the reference-bound and jet-comparison
paragraphs. Radial normalization is smooth on the open set where every factor
is nonzero. Composing the same native selector with this map gives an actual
ambient function, with every derivative bounded on the compact product of unit
spheres. The constants are selected without any initialization frequency,
cutoff, chart count, or source manifold as inputs.
-/

noncomputable section
open Set TopologicalSpace NormedSpace
open scoped Manifold ContDiff

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

abbrev HopfProductAmbient {a : ℕ} (C : Fin a → ℕ) :=
  ∀ i, PlanarHopfAmbient (C i)

/-- The literal factorwise inclusion of the whole Hopf product. -/
def hopfProductInclusion {a : ℕ} (C : Fin a → ℕ)
    (z : FreeHopfProduct C) : HopfProductAmbient C := fun i ↦ z i

theorem hopfProductInclusion_continuous {a : ℕ} (C : Fin a → ℕ) :
    Continuous (hopfProductInclusion C) := by
  exact continuous_pi fun i ↦ continuous_subtype_val.comp (continuous_apply i)

/-- The actual open radial domain, with its inherited ordinary manifold. -/
def hopfRadialDomain {a : ℕ} (C : Fin a → ℕ) : Opens (HopfProductAmbient C) where
  carrier := {z | ∀ i, z i ≠ 0}
  is_open' := by
    simpa only [Set.iInter_ofPred] using
      (isOpen_iInter_of_finite fun i : Fin a ↦
        isOpen_ne_fun (continuous_apply (A := fun i ↦ PlanarHopfAmbient (C i)) i)
          continuous_const)

/-- Radial projection into the native spheres, not a formal sphere constraint. -/
def hopfRadialProjection {a : ℕ} (C : Fin a → ℕ)
    (z : hopfRadialDomain C) : FreeHopfProduct C := fun i ↦
  ⟨NormedSpace.normalize ((z : HopfProductAmbient C) i),
    mem_sphere_zero_iff_norm.mpr (norm_normalize (z.property i))⟩

theorem hopfRadialProjection_contMDiff {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] :
    ContMDiff 𝓘(ℝ, HopfProductAmbient C) (freeHopfModel C) ∞
      (hopfRadialProjection C) := by
  rw [show freeHopfModel C = ModelWithCorners.pi (fun i ↦ planarHopfModel (C i)) from
    (free_finite_product_model_eq _).symm]
  apply contMDiff_pi_iff.2
  intro i
  apply ContMDiff.codRestrict_sphere
  have hp : ContMDiff 𝓘(ℝ, HopfProductAmbient C) 𝓘(ℝ, PlanarHopfAmbient (C i)) ∞
      (fun z : hopfRadialDomain C ↦ (z : HopfProductAmbient C) i) :=
    (contDiff_apply ℝ (fun i ↦ PlanarHopfAmbient (C i)) i).contMDiff.comp
      contMDiff_subtype_val
  have hn : ContMDiff 𝓘(ℝ, HopfProductAmbient C) 𝓘(ℝ, ℝ) ∞
      (fun z : hopfRadialDomain C ↦ ‖(z : HopfProductAmbient C) i‖) := by
    intro z
    exact (contDiffAt_norm ℂ (z.property i)).comp_contMDiffAt (hp z)
  exact (hn.inv₀ (fun z ↦ norm_ne_zero_iff.mpr (z.property i))).smul hp

theorem hopfProductInclusion_mem_radial {a : ℕ} (C : Fin a → ℕ)
    (z : FreeHopfProduct C) : hopfProductInclusion C z ∈ hopfRadialDomain C := by
  intro i
  exact ne_zero_of_mem_unit_sphere (z i)

@[simp] theorem hopfRadialProjection_inclusion {a : ℕ} (C : Fin a → ℕ)
    (z : FreeHopfProduct C) :
    hopfRadialProjection C
      ⟨hopfProductInclusion C z, hopfProductInclusion_mem_radial C z⟩ = z := by
  funext i
  apply Subtype.ext
  exact normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp (z i).property)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual selector composed with radial projection, extended arbitrarily by
zero only outside the open radial domain. Its germ on every sphere point is fixed. -/
def selectorAmbientExtension {a : ℕ} (C : Fin a → ℕ)
    (S : FreeHopfProduct C → F) : HopfProductAmbient C → F :=
  Function.extend (Subtype.val : hopfRadialDomain C → HopfProductAmbient C)
    (S ∘ hopfRadialProjection C) (fun _ ↦ 0)

theorem selectorAmbientExtension_on_radial {a : ℕ} (C : Fin a → ℕ)
    (S : FreeHopfProduct C → F) (z : hopfRadialDomain C) :
    selectorAmbientExtension C S z = S (hopfRadialProjection C z) :=
  Subtype.val_injective.extend_apply _ _ z

@[simp] theorem selectorAmbientExtension_inclusion {a : ℕ} (C : Fin a → ℕ)
    (S : FreeHopfProduct C → F) (z : FreeHopfProduct C) :
    selectorAmbientExtension C S (hopfProductInclusion C z) = S z := by
  rw [selectorAmbientExtension_on_radial C S
    ⟨hopfProductInclusion C z, hopfProductInclusion_mem_radial C z⟩]
  rw [hopfRadialProjection_inclusion]

theorem selectorAmbientExtension_contDiffAt {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    {z : HopfProductAmbient C} (hz : z ∈ hopfRadialDomain C) :
    ContDiffAt ℝ ∞ (selectorAmbientExtension C S) z := by
  have hs := hS.comp (hopfRadialProjection_contMDiff C)
  have heq : (fun x : hopfRadialDomain C ↦ selectorAmbientExtension C S x) =
      S ∘ hopfRadialProjection C := by
    funext x
    exact selectorAmbientExtension_on_radial C S x
  have hsub : ContMDiffAt 𝓘(ℝ, HopfProductAmbient C) 𝓘(ℝ, F) ∞
      (fun x : hopfRadialDomain C ↦ selectorAmbientExtension C S x) ⟨z, hz⟩ := by
    rw [heq]
    exact hs _
  exact (contMDiffAt_subtype_iff.mp hsub).contDiffAt

/-- Every reference derivative of the same explicit extension has one bound on
the whole product, chosen before any K,T or source preparation. Empty products
and arbitrary target normed spaces are allowed. -/
theorem selectorAmbientExtension_uniform_derivatives {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧ ∀ j z,
      ‖iteratedFDeriv ℝ j (selectorAmbientExtension C S)
        (hopfProductInclusion C z)‖ ≤ B j := by
  have hb (j : ℕ) : ∃ b : ℝ, ∀ z : FreeHopfProduct C,
      ‖iteratedFDeriv ℝ j (selectorAmbientExtension C S)
        (hopfProductInclusion C z)‖ ≤ b := by
    have hc : Continuous (fun z : FreeHopfProduct C ↦
        iteratedFDeriv ℝ j (selectorAmbientExtension C S) (hopfProductInclusion C z)) := by
      apply continuous_iff_continuousAt.2
      intro z
      exact ((selectorAmbientExtension_contDiffAt C S hS
        (hopfProductInclusion_mem_radial C z)).continuousAt_iteratedFDeriv
          (show (j : ℕ∞ω) ≤ ∞ by simp)).comp
            (hopfProductInclusion_continuous C).continuousAt
    obtain ⟨b, hb⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨b, fun z ↦ hb z (mem_univ z)⟩
  choose b hb using hb
  refine ⟨fun j ↦ max 1 (b j), fun j ↦ lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro j z
  exact (hb j z).trans (le_max_right _ _)

end GlobalEmbedding.Initialization
