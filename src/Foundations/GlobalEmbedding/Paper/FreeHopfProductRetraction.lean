import GlobalEmbedding.Paper.FreeHopfProductNative
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# An actual smooth radial ambient neighborhood of the whole Hopf product

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines216–232 and403–418.
DAG node: `free-hopf-product-retraction`.
-/

noncomputable section

open Set NormedSpace
open scoped Manifold ContDiff Topology

namespace GlobalEmbedding.Paper

/-- The actual product of the original complex ambient spaces, viewed over the reals. -/
abbrev FreeHopfAmbientSpace {a : ℕ} (C : Fin a → ℕ) := ∀ i, PlanarHopfAmbient (C i)

/-- The actual whole-product ambient inclusion. -/
def freeHopfAmbientInclusion {a : ℕ} (C : Fin a → ℕ)
    (x : FreeHopfProduct C) : FreeHopfAmbientSpace C := fun i ↦ (x i).val

/-- The genuine ambient open set on which every factor admits radial normalization. -/
def freeHopfAmbientDomain {a : ℕ} (C : Fin a → ℕ) :
    TopologicalSpace.Opens (FreeHopfAmbientSpace C) :=
  ⟨{z | ∀ i, z i ≠ 0}, by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i ↦ isOpen_compl_singleton.preimage
      (continuous_apply i))⟩

/-- The actual radial retraction into genuine sphere factors. No orbit origin is chosen. -/
def freeHopfRadialRetraction {a : ℕ} (C : Fin a → ℕ)
    (z : freeHopfAmbientDomain C) : FreeHopfProduct C := fun i ↦
  ⟨normalize (z.val i), mem_sphere_zero_iff_norm.mpr (norm_normalize (z.property i))⟩

/-- The actual product inclusion is native smooth into the original ambient vector space. -/
theorem freeHopfAmbientInclusion_contMDiff {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] :
    ContMDiff (freeHopfModel C) 𝓘(ℝ, FreeHopfAmbientSpace C) ∞
      (freeHopfAmbientInclusion C) := by
  apply contMDiff_pi_module_iff.2
  intro i
  exact (planarHopfSphere_contMDiff_coe (C i)).comp (freeHopfProduct_contMDiff_apply C i)

/-- Every genuine sphere-product point lies in the actual radial domain. -/
theorem freeHopfAmbientInclusion_mem {a : ℕ} (C : Fin a → ℕ)
    (x : FreeHopfProduct C) : freeHopfAmbientInclusion C x ∈ freeHopfAmbientDomain C :=
  fun i ↦ ne_zero_of_mem_unit_sphere (x i)

/-- Radial normalization is exactly identity on the actual whole product. -/
theorem freeHopfRadialRetraction_inclusion {a : ℕ} (C : Fin a → ℕ)
    (x : FreeHopfProduct C) :
    freeHopfRadialRetraction C
      ⟨freeHopfAmbientInclusion C x, freeHopfAmbientInclusion_mem C x⟩ = x := by
  funext i
  apply Subtype.ext
  exact normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp (x i).property)

/-- The true radial retraction is globally native smooth on its actual open domain.

Proof: coordinate normalization is norm-inverse times the actual vector. The real norm
is smooth away from zero in the genuine complex inner-product ambient space; the domain
ensures that exact nonzero condition. Actual open-subtype inclusion transports the smooth
ambient normalization to the domain. The genuine sphere codomain criterion and finite Pi
smoothness criterion then give the actual native product map. Empty products are included.
Source: the finite-dimensional compact-parameter correction in lem:balanced, lines403–418,
applied to the actual sphere product in setup:partial. -/
theorem freeHopfRadialRetraction_contMDiff {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] :
    ContMDiff 𝓘(ℝ, FreeHopfAmbientSpace C) (freeHopfModel C) ∞
      (freeHopfRadialRetraction C) := by
  rw [show freeHopfModel C = ModelWithCorners.pi (fun i ↦ planarHopfModel (C i)) from
    (free_finite_product_model_eq _).symm]
  apply contMDiff_pi_iff.2
  intro i
  apply ContMDiff.codRestrict_sphere
  intro z
  have hv : ContDiffAt ℝ ∞ (fun w : FreeHopfAmbientSpace C ↦ w i) z.val :=
    (contDiff_apply ℝ (fun i ↦ PlanarHopfAmbient (C i)) i).contDiffAt
  have hn := hv.norm ℂ (z.property i)
  have hi := hn.inv (norm_ne_zero_iff.mpr (z.property i))
  have hs := hi.smul hv
  exact hs.contMDiffAt.comp z (contMDiff_subtype_val z)

/-- The actual finite-dimensional ambient parameter set is compact, with no extra bound. -/
theorem freeHopfAmbientInclusion_isCompact_range {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] :
    IsCompact (Set.range (freeHopfAmbientInclusion C)) :=
  isCompact_range (freeHopfAmbientInclusion_contMDiff C).continuous

/-- The entire true compact parameter set lies inside the genuine radial open set. -/
theorem freeHopfAmbientInclusion_range_subset {a : ℕ} (C : Fin a → ℕ) :
    Set.range (freeHopfAmbientInclusion C) ⊆ freeHopfAmbientDomain C := by
  rintro z ⟨x, rfl⟩
  exact freeHopfAmbientInclusion_mem C x

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopfRadialRetraction_contMDiff
#print axioms GlobalEmbedding.Paper.freeHopfRadialRetraction_inclusion
#print axioms GlobalEmbedding.Paper.freeHopfAmbientInclusion_isCompact_range
