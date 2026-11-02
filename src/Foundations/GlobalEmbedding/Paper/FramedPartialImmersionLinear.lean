import GlobalEmbedding.External.SphereEversion.Local.DualPair
import Mathlib.Analysis.Convex.AmpleSet

/-!
# Principal slices for partial immersions

Source: `literature/parallelizable-stable-plus-one/main.tex`, Lemma `lem:planar`,
first paragraph of the proof. Restrict the actual provider update to the prescribed
distribution. A normalized vector in that distribution supplies its own dual pair;
the allowed update is the complement of a translated image of a hyperplane.
-/

namespace GlobalEmbedding.Paper

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The principal covector restricted to a subspace, normalized by an actual vector. -/
def framedPartialDualPair (p : DualPair E) (V : Submodule ℝ E) (u : V)
    (hu : p.π u = 1) : DualPair V where
  π := p.π.comp V.subtypeL
  v := u
  pairing := hu

/-- The provider update restricted to the distribution is an actual update on that subspace.
Its free value includes the affine translation from the two different normalized vectors. -/
theorem framedPartial_update_restrict (p : DualPair E) (V : Submodule ℝ E) (u : V)
    (hu : p.π u = 1) (φ : E →L[ℝ] F) (w : F) :
    (p.update φ w).comp V.subtypeL =
      (framedPartialDualPair p V u hu).update (φ.comp V.subtypeL)
        (φ u + (w - φ p.v)) := by
  ext x
  simp [DualPair.update, framedPartialDualPair]

/-- The forbidden affine derivative values for injectivity on the distribution. -/
theorem framedPartial_update_injective_iff (p : DualPair E) (V : Submodule ℝ E) (u : V)
    (hu : p.π u = 1) {φ : E →L[ℝ] F} (hφ : Function.Injective (φ.comp V.subtypeL))
    (w : F) :
    Function.Injective ((p.update φ w).comp V.subtypeL) ↔
      φ u + (w - φ p.v) ∉
        (framedPartialDualPair p V u hu).π.ker.map (φ.comp V.subtypeL).toLinearMap := by
  rw [framedPartial_update_restrict p V u hu]
  exact (framedPartialDualPair p V u hu).injective_update_iff hφ

/-- If the prescribed distribution lies in the fixed hyperplane, every update preserves it. -/
theorem framedPartial_update_restrict_of_le_ker (p : DualPair E) (V : Submodule ℝ E)
    (hD : V ≤ p.π.ker) (φ : E →L[ℝ] F) (w : F) :
    (p.update φ w).comp V.subtypeL = φ.comp V.subtypeL := by
  ext x
  exact p.update_ker_pi φ w (hD x.property)

/-- The entire principal slice is allowed if the fixed hyperplane contains the distribution. -/
theorem framedPartial_slice_eq_univ_of_le_ker (p : DualPair E) (V : Submodule ℝ E)
    (hV : V ≤ p.π.ker) {φ : E →L[ℝ] F} (hφ : Function.Injective (φ.comp V.subtypeL)) :
    {w : F | Function.Injective ((p.update φ w).comp V.subtypeL)} = Set.univ := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  rwa [framedPartial_update_restrict_of_le_ker p V hV]

/-- A nonzero principal covector on the distribution has an actual normalized vector. -/
theorem framedPartial_exists_normalized (p : DualPair E) (V : Submodule ℝ E)
    (hV : ¬ V ≤ p.π.ker) : ∃ u : V, p.π u = 1 := by
  classical
  by_contra h
  apply hV
  intro v hv
  change p.π v = 0
  by_contra hv0
  apply h
  refine ⟨⟨(p.π v)⁻¹ • v, V.smul_mem _ hv⟩, ?_⟩
  simp [hv0]

/-- A codimension-two kernel image gives an ample partial-immersion slice, with its actual
affine translation. The dimensional estimate is supplied separately from the frame rank. -/
theorem framedPartial_slice_ample_of_codim (p : DualPair E) (V : Submodule ℝ E) (u : V)
    (hu : p.π u = 1) {φ : E →L[ℝ] F} (hφ : Function.Injective (φ.comp V.subtypeL))
    (hcodim : 1 < Module.rank ℝ
      (F ⧸ (framedPartialDualPair p V u hu).π.ker.map (φ.comp V.subtypeL).toLinearMap)) :
    AmpleSet {w : F | Function.Injective ((p.update φ w).comp V.subtypeL)} := by
  let S := (framedPartialDualPair p V u hu).π.ker.map (φ.comp V.subtypeL).toLinearMap
  have hEq : {w : F | Function.Injective ((p.update φ w).comp V.subtypeL)} =
      (ContinuousAffineEquiv.constVAdd ℝ F (φ u - φ p.v)) ⁻¹' (S : Set F)ᶜ := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff]
    rw [framedPartial_update_injective_iff p V u hu hφ]
    change φ u + (w - φ p.v) ∉ S ↔ (φ u - φ p.v) + w ∉ S
    have ht : φ u + (w - φ p.v) = (φ u - φ p.v) + w := by abel
    rw [ht]
  rw [hEq]
  exact (AmpleSet.of_one_lt_codim hcodim).preimage
    (ContinuousAffineEquiv.constVAdd ℝ F (φ u - φ p.v))

/-- A hyperplane image has codimension at least two when the target has larger dimension.
Proof reused from sphere-eversion commit `33ab3d626854a0f0f04ed5772e3102d652e96475`,
`ToMathlib/LinearAlgebra/FiniteDimensional.lean`, `one_lt_rank_of_rank_lt_rank`.
Only names are adapted; the dimension argument is unchanged. -/
theorem framedPartial_kernelImage_codim [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (p : DualPair E) (h : Module.finrank ℝ E < Module.finrank ℝ F) (φ : E →L[ℝ] F) :
    1 < Module.rank ℝ (F ⧸ p.π.ker.map φ.toLinearMap) := by
  suffices 2 ≤ Module.finrank ℝ (F ⧸ p.π.ker.map φ.toLinearMap) by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast this
  apply le_of_add_le_add_right
  rw [Submodule.finrank_quotient_add_finrank (p.π.ker.map φ.toLinearMap)]
  have := calc Module.finrank ℝ (p.π.ker.map φ.toLinearMap)
      _ ≤ Module.finrank ℝ p.π.ker := Submodule.finrank_map_le φ.toLinearMap p.π.ker
      _ < Module.finrank ℝ E := Submodule.finrank_lt p.ker_pi_ne_top
  linarith

/-- The actual slice of injectivity on any lower-dimensional subspace is ample. -/
theorem framedPartial_slice_ample [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (p : DualPair E) (V : Submodule ℝ E)
    (h : Module.finrank ℝ V < Module.finrank ℝ F) {φ : E →L[ℝ] F}
    (hφ : Function.Injective (φ.comp V.subtypeL)) :
    AmpleSet {w : F | Function.Injective ((p.update φ w).comp V.subtypeL)} := by
  by_cases hV : V ≤ p.π.ker
  · rw [framedPartial_slice_eq_univ_of_le_ker p V hV hφ]
    exact ampleSet_univ
  obtain ⟨u, hu⟩ := framedPartial_exists_normalized p V hV
  apply framedPartial_slice_ample_of_codim p V u hu hφ
  exact framedPartial_kernelImage_codim (framedPartialDualPair p V u hu) h (φ.comp V.subtypeL)

end GlobalEmbedding.Paper
