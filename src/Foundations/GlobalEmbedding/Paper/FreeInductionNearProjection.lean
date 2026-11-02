import GlobalEmbedding.Paper.FreeInductionEuclideanBlocks
import GlobalEmbedding.Paper.MatrixPlanarSelectorProperties
import GlobalEmbedding.Paper.FreeSecondCancellationRows
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The actual induction near-patch orthogonal projection

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 477–489.
The projection below uses the sole genuine Euclidean induction block map.
Full actual normalized-column rank and compact-buffer instantiation remain under construction.
-/

noncomputable section
open scoped ContDiff Manifold

namespace GlobalEmbedding.Paper

/-- The actual near-patch projection off the embedded planar J₂v, in the same target as F₀/Z/W. -/
def freeInductionNearProjection (K m : ℕ) (v : Planar) :
    EuclideanSpace ℝ (Fin (K + (2 + m))) →L[ℝ]
      EuclideanSpace ℝ (Fin (K + (2 + m))) :=
  (ℝ ∙ freeInductionBlock K m 0 (planarQuarterTurn v) 0)ᗮ.starProjection

/-- The actual projection is self-adjoint; no substitute symmetric operator is supplied. -/
theorem freeInductionNearProjection_adjoint (K m : ℕ) (v : Planar) :
    (freeInductionNearProjection K m v).adjoint = freeInductionNearProjection K m v :=
  (ℝ ∙ freeInductionBlock K m 0 (planarQuarterTurn v) 0)ᗮ.starProjection_isSymmetric.clm_adjoint_eq

/-- Its true operator norm is at most one, as required by normalized-column correction estimates. -/
theorem freeInductionNearProjection_norm_le (K m : ℕ) (v : Planar) :
    ‖freeInductionNearProjection K m v‖ ≤ 1 :=
  (ℝ ∙ freeInductionBlock K m 0 (planarQuarterTurn v) 0)ᗮ.starProjection_norm_le

/-- The entire actual base active second column is killed, with no division by curvature. -/
theorem freeInductionNearProjection_active_base (K m : ℕ) (v : Planar) (κ : ℝ) :
    freeInductionNearProjection K m v
      (κ • freeInductionBlock K m 0 (planarQuarterTurn v) 0) = 0 := by
  rw [map_smul]
  simp only [freeInductionNearProjection,
    Submodule.starProjection_orthogonalComplement_singleton_eq_zero, smul_zero]

/-- The actual embedded quarter-turned velocity is a unit vector whenever the actual velocity is. -/
theorem freeInductionNearProjection_unit_direction (K m : ℕ) (v : Planar) (hv : ‖v‖ = 1) :
    ‖freeInductionBlock K m 0 (planarQuarterTurn v) 0‖ = 1 := by
  have hq : inner ℝ (planarQuarterTurn v) (planarQuarterTurn v) = inner ℝ v v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    simp [planarQuarterTurn, dotProduct, Fin.sum_univ_two]
    ring
  have h : ‖freeInductionBlock K m 0 (planarQuarterTurn v) 0‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, freeInductionBlock_inner]
    simp only [inner_zero_left, zero_add, add_zero, hq, real_inner_self_eq_norm_sq, hv, one_pow]
  nlinarith [norm_nonneg (freeInductionBlock K m 0 (planarQuarterTurn v) 0)]

/-- The actual projection has its literal unit-vector formula. This identity will supply native
smoothness through curvature zeros, where the vector J₂v remains unit. -/
theorem freeInductionNearProjection_apply (K m : ℕ) (v : Planar) (hv : ‖v‖ = 1)
    (u : EuclideanSpace ℝ (Fin (K + (2 + m)))) :
    freeInductionNearProjection K m v u =
      u - inner ℝ (freeInductionBlock K m 0 (planarQuarterTurn v) 0) u •
        freeInductionBlock K m 0 (planarQuarterTurn v) 0 := by
  rw [freeInductionNearProjection, Submodule.starProjection_orthogonal]
  simp [Submodule.starProjection_singleton, freeInductionNearProjection_unit_direction K m v hv]

/-- Old and complement blocks are genuinely fixed by the projection. Orthogonality follows from
the actual Euclidean block inner product, including all appended coordinates. -/
theorem freeInductionNearProjection_fix_complement (K m : ℕ) (v : Planar) (hv : ‖v‖ = 1)
    (h : EuclideanSpace ℝ (Fin K)) (r : EuclideanSpace ℝ (Fin m)) :
    freeInductionNearProjection K m v (freeInductionBlock K m h 0 r) =
      freeInductionBlock K m h 0 r := by
  rw [freeInductionNearProjection_apply K m v hv, freeInductionBlock_inner]
  simp

/-- The actual base active first column v survives the projection off J₂v. -/
theorem freeInductionNearProjection_fix_velocity (K m : ℕ) (v : Planar) (hv : ‖v‖ = 1) :
    freeInductionNearProjection K m v (freeInductionBlock K m 0 v 0) =
      freeInductionBlock K m 0 v 0 := by
  have horth : inner ℝ (planarQuarterTurn v) v = 0 := by
    simp [planarQuarterTurn, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_two]
    ring
  rw [freeInductionNearProjection_apply K m v hv, freeInductionBlock_inner]
  simp [horth]

variable {P H M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] {I : ModelWithCorners ℝ P H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The actual near projection is globally native smooth through every curvature zero.
The unit velocity keeps its direction nonzero; the genuine rank-one formula proves smoothness. -/
theorem freeInductionNearProjection_contMDiff (K m : ℕ) (v : M → Planar)
    (hv : ContMDiff I 𝓘(ℝ, Planar) ∞ v) (hunit : ∀ x, ‖v x‖ = 1) :
    ContMDiff I
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m))) →L[ℝ]
        EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞
      (fun x ↦ freeInductionNearProjection K m (v x)) := by
  have hJ : ContMDiff I 𝓘(ℝ, Planar) ∞ (fun x ↦ planarQuarterTurn (v x)) := by
    have hh := freePlanarSecondCorrection_contMDiff v (fun _ ↦ 0) (fun _ ↦ 1)
      hv contMDiff_const contMDiff_const
    change ContMDiff I 𝓘(ℝ, Planar) ∞
      (fun x ↦ (0 : ℝ) • v x + (1 : ℝ) • planarQuarterTurn (v x)) at hh
    simpa only [zero_smul, one_smul, zero_add] using hh
  have hw := freeInductionBlock_contMDiff K m
    (fun _ : M ↦ 0) (fun x ↦ planarQuarterTurn (v x)) (fun _ : M ↦ 0)
    contMDiff_const hJ contMDiff_const
  intro x
  apply (manifold_finite_operator_smooth_iff _ x).mpr
  intro u
  have hi : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y ↦ inner ℝ (freeInductionBlock K m 0 (planarQuarterTurn (v y)) 0) u) := by
    have hh := (innerSL ℝ u).contDiff.contMDiff.comp hw
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using hh
  have happ := (contMDiff_const (c := u)).sub (hi.smul hw)
  have heq : (fun y ↦ freeInductionNearProjection K m (v y) u) =
      fun y ↦ u - inner ℝ (freeInductionBlock K m 0 (planarQuarterTurn (v y)) 0) u •
        freeInductionBlock K m 0 (planarQuarterTurn (v y)) 0 :=
    funext fun y ↦ freeInductionNearProjection_apply K m (v y) (hunit y) u
  rw [heq]
  exact happ.contMDiffAt

/-- The same actual planar selector supplies both the genuine velocity smoothness and its unit
length, so no projector or projector regularity is a premise of this actual Hopf construction. -/
theorem freeInductionNearProjection_selector_contMDiff (K m C : ℕ) [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f) :
    ContMDiff (planarHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m))) →L[ℝ]
        EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞
      (fun z ↦ freeInductionNearProjection K m (orbitDeriv planarHopfFlow f z)) :=
  freeInductionNearProjection_contMDiff K m _
    (contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf.smooth) hf.unit_speed

#print axioms freeInductionNearProjection_adjoint
#print axioms freeInductionNearProjection_active_base
#print axioms freeInductionNearProjection_apply
#print axioms freeInductionNearProjection_fix_complement
#print axioms freeInductionNearProjection_fix_velocity
#print axioms freeInductionNearProjection_selector_contMDiff

end GlobalEmbedding.Paper
