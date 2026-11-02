import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Native finite products of ordinary smooth manifolds

Source: `literature/parallelizable-stable-plus-one/main.tex`, setup:partial, lines216–232.
DAG node: `free-finite-product-manifold`.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The actual finite Pi atlas, with its model type read as the ordinary Pi vector space. -/
abbrev freeFiniteProductChartedSpace {ι : Type*} [Fintype ι]
    (E M : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (E i) (M i)] :
    ChartedSpace (∀ i, E i) (∀ i, M i) := piChartedSpace E M

/-- A finite product of identity models is the ordinary identity model on the Pi space. -/
theorem free_finite_product_model_eq {ι : Type*} [Fintype ι]
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] :
    ModelWithCorners.pi (fun i ↦ 𝓘(ℝ, E i)) = 𝓘(ℝ, ∀ i, E i) := by
  ext1 <;> simp [ModelWithCorners.pi]

/-- The genuine finite product atlas is smooth for the ordinary product vector model.

Proof: every product-atlas chart is a finite product of actual factor charts. Its actual
transition has components equal to the factor transitions composed with coordinate
projections. Factor atlas compatibility and the finite Pi smoothness criterion therefore
give every product transition. The empty product is included by the same Pi criterion.
Source: the smooth Hopf product in setup:partial, lines216–232. -/
theorem free_finite_product_isManifold {ι : Type*} [Fintype ι]
    (E M : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (E i) (M i)]
    (n : ℕ∞ω) [∀ i, IsManifold 𝓘(ℝ, E i) n (M i)] :
    let _ := freeFiniteProductChartedSpace E M
    IsManifold 𝓘(ℝ, ∀ i, E i) n (∀ i, M i) := by
  let _ := freeFiniteProductChartedSpace E M
  apply isManifold_of_contDiffOn
  rintro e e' ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ]
  apply contDiffOn_pi.2
  intro i
  have hfg := ((contDiffGroupoid n 𝓘(ℝ, E i)).compatible
    (hf i (mem_univ i)) (hg i (mem_univ i))).1
  have ht : ContDiffOn ℝ n ((f i).symm.trans (g i))
      ((f i).symm.trans (g i)).source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id,
      Set.inter_univ] using hfg
  exact ht.comp (contDiff_apply ℝ E i).contDiffOn (by
    intro x hx
    exact ⟨hx.1 i (mem_univ i), hx.2 i (mem_univ i)⟩)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.free_finite_product_isManifold
#print axioms GlobalEmbedding.Paper.free_finite_product_model_eq
