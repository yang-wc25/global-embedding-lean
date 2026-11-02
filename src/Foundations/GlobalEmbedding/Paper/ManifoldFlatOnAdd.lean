import GlobalEmbedding.Paper.ManifoldFlatOn
import GlobalEmbedding.Paper.GeneralMaximalChartTargetOpen
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Addition, subtraction and negation of actual fully flat functions

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines355–366.
All full jets in the actual maximal smooth atlas vanish, including order zero.
-/

open Manifold
open scoped Manifold ContDiff Topology

namespace GlobalEmbedding.Paper

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f g : M → F} {Z : Set M}

/-- The sum of two actually fully flat maps is fully flat in every native smooth chart. -/
theorem manifold_flat_on_add (hf : ManifoldFlatOn (I := I) f Z)
    (hg : ManifoldFlatOn (I := I) g Z) :
    ManifoldFlatOn (I := I) (fun x ↦ f x + g x) Z := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro x hx e he hex k
  have he2 : e ∈ IsManifold.maximalAtlas I 2 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hopen := general_maximal_chart_target_open e he2
  have hInv : ContMDiffOn 𝓘(ℝ, E) I ∞ (e.extend I).symm (e.extend I).target := by
    simpa only [OpenPartialHomeomorph.extend_target, I.image_eq] using
      contMDiffOn_extend_symm (e := e) he
  have hmem : e.extend I x ∈ (e.extend I).target :=
    (e.extend I).map_source (by simpa only [OpenPartialHomeomorph.extend_source] using hex)
  have hfi : ContDiffAt ℝ k (f ∘ (e.extend I).symm) (e.extend I x) :=
    (((hf.1.comp_contMDiffOn hInv).contDiffOn).contDiffAt
      (hopen.mem_nhds hmem)).of_le (by simp)
  have hgi : ContDiffAt ℝ k (g ∘ (e.extend I).symm) (e.extend I x) :=
    (((hg.1.comp_contMDiffOn hInv).contDiffOn).contDiffAt
      (hopen.mem_nhds hmem)).of_le (by simp)
  change iteratedFDeriv ℝ k
    ((f ∘ (e.extend I).symm) + (g ∘ (e.extend I).symm)) (e.extend I x) = 0
  rw [iteratedFDeriv_add_apply hfi hgi, hf.2 x hx e he hex k, hg.2 x hx e he hex k,
    add_zero]

/-- Negation preserves every actual zero chart jet. -/
theorem manifold_flat_on_neg (hf : ManifoldFlatOn (I := I) f Z) :
    ManifoldFlatOn (I := I) (fun x ↦ -f x) Z := by
  refine ⟨hf.1.neg, ?_⟩
  intro x hx e he hex k
  change iteratedFDeriv ℝ k (-(f ∘ (e.extend I).symm)) (e.extend I x) = 0
  rw [iteratedFDeriv_neg_apply, hf.2 x hx e he hex k, neg_zero]

/-- Subtraction preserves all actual native flat jets. -/
theorem manifold_flat_on_sub (hf : ManifoldFlatOn (I := I) f Z)
    (hg : ManifoldFlatOn (I := I) g Z) :
    ManifoldFlatOn (I := I) (fun x ↦ f x - g x) Z := by
  simpa only [sub_eq_add_neg] using manifold_flat_on_add hf (manifold_flat_on_neg hg)

#print axioms manifold_flat_on_add
#print axioms manifold_flat_on_neg
#print axioms manifold_flat_on_sub

end GlobalEmbedding.Paper
