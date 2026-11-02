import GlobalEmbedding.Paper.FullTangentFrame
import GlobalEmbedding.Paper.SmoothPositiveMatrixRoot
import GlobalEmbedding.Paper.PositiveRootOrthonormalization
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Smooth positive-root normalization of a full tangent frame

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, proof line 798. The actual Gram matrix of the given smooth
frame has a smooth positive root. Multiplication by its inverse gives a smooth
orthonormal frame, and metric pairing gives the dual smooth coframe.
-/

open scoped Manifold ContDiff Bundle MatrixOrder Matrix.Norms.L2Operator
open Bundle Matrix

noncomputable section
namespace GlobalEmbedding.Paper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ}

/-- The actual Gram matrix in the specified smooth metric and full frame. -/
def fullFrameGram
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ g.inner x (f.framed.frame i x) (f.framed.frame j x)

private theorem fullFrameGram_entry_smooth
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (i j : Fin n) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ fullFrameGram I g f x i j) := by
  intro x
  have h := (g.contMDiff.clm_bundle_apply₂ (f.framed.frame i).contMDiff
    (f.framed.frame j).contMDiff).contMDiffAt (x := x)
  simp only [contMDiffAt_totalSpace] at h
  exact h.2

private theorem fullFrameGram_smooth
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) :
    ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ (fullFrameGram I g f) := by
  have h : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞
      (fun x ↦ ∑ i, ∑ j, fullFrameGram I g f x i j • Matrix.single i j (1 : ℝ)) :=
    .sum fun i _ ↦ .sum fun j _ ↦
      (fullFrameGram_entry_smooth I g f i j).smul contMDiff_const
  convert h using 1
  funext x i j
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

private theorem fullFrameGram_selfAdjoint
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) :
    IsSelfAdjoint (fullFrameGram I g f x) := by
  ext i j
  change fullFrameGram I g f x j i = fullFrameGram I g f x i j
  exact
    g.symm x (f.framed.frame j x) (f.framed.frame i x)

/-- The Gram matrix as an element of the actual symmetric matrix subspace. -/
def fullFrameSymmetricGram
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) :
    selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  ⟨fullFrameGram I g f x, fullFrameGram_selfAdjoint I g f x⟩

private theorem fullFrameSymmetricGram_smooth
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) :
    ContMDiff I 𝓘(ℝ, selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) ∞
      (fullFrameSymmetricGram I g f) := by
  let S := selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)
  let proj : Matrix (Fin n) (Fin n) ℝ →L[ℝ] S :=
    (((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ _ +
      (starL' ℝ : Matrix (Fin n) (Fin n) ℝ ≃L[ℝ] _).toContinuousLinearMap)).codRestrict S (by
        intro X
        change star ((2 : ℝ)⁻¹ • (X + star X)) = (2 : ℝ)⁻¹ • (X + star X)
        simp only [star_smul, star_trivial, star_add, star_star]
        rw [add_comm])
  have h := proj.contDiff.comp_contMDiff (fullFrameGram_smooth I g f)
  convert h using 1
  funext x
  apply Subtype.ext
  change fullFrameGram I g f x = (2 : ℝ)⁻¹ •
    (fullFrameGram I g f x + star (fullFrameGram I g f x))
  rw [(fullFrameGram_selfAdjoint I g f x).star_eq, ← two_smul ℝ _, smul_smul]
  norm_num

private theorem fullFrameGram_posDef
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) :
    (fullFrameGram I g f x).PosDef := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Matrix.posDef_gram_of_linearIndependent (f.framed.independent x)

/-- The actual positive square root of the full frame's Gram matrix. -/
def fullFrameGramRoot
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) : Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt (fullFrameGram I g f x)

private theorem fullFrameGramRoot_smooth
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) :
    ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ (fullFrameGramRoot I g f) ∧
      ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞
        (fun x ↦ (fullFrameGramRoot I g f x)⁻¹) := by
  have h (x : M) := smooth_positive_matrix_root (fullFrameSymmetricGram I g f x)
    (fullFrameGram_posDef I g f x)
  exact ⟨fun x ↦ (h x).2.2.2.1.comp_contMDiffAt
      (fullFrameSymmetricGram_smooth I g f).contMDiffAt,
    fun x ↦ (h x).2.2.2.2.1.comp_contMDiffAt
      (fullFrameSymmetricGram_smooth I g f).contMDiffAt⟩

private theorem fullFrameGramRoot_inv_entry_smooth
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (i j : Fin n) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ (fullFrameGramRoot I g f x)⁻¹ i j) := by
  let ev : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun A ↦ A i j
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact ev.toContinuousLinearMap.contDiff.comp_contMDiff (fullFrameGramRoot_smooth I g f).2

/-- The normalized fields are the columns of `f * sqrt(Gram(f))⁻¹`. -/
def positiveRootFrameSection
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (i : Fin n) :
    ContMDiffSection I E ∞ (TangentSpace I : M → Type _) where
  toFun x := ∑ j, (fullFrameGramRoot I g f x)⁻¹ j i • f.framed.frame j x
  contMDiff_toFun := .sum_section fun j _ ↦
    (fullFrameGramRoot_inv_entry_smooth I g f j i).smul_section (f.framed.frame j).contMDiff

/-- Pointwise orthonormality, full span, and reconstruction for the actual smooth
positive-root fields. This is the accepted matrix theorem applied in each actual
metric tangent fiber. -/
theorem positiveRootFrameSection_properties
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ x : M, Orthonormal ℝ (fun i ↦ positiveRootFrameSection I g f i x) ∧
      Submodule.span ℝ (Set.range fun i ↦ positiveRootFrameSection I g f i x) = ⊤ ∧
      ∀ j, ∑ i, fullFrameGramRoot I g f x i j •
        positiveRootFrameSection I g f i x = f.framed.frame j x := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro x
  have h := positive_root_orthonormalization (fun i ↦ f.framed.frame i x)
    (f.framed.independent x)
  refine ⟨h.1, ?_, h.2.2⟩
  exact h.2.1.trans (f.spans x)

/-- The smooth full tangent frame obtained from the actual positive Gram root. -/
def positiveRootFullFrame
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) : FullTangentFrame I (M := M) n where
  framed :=
    { frame := positiveRootFrameSection I g f
      independent := by
        letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
        exact fun x ↦ (positiveRootFrameSection_properties I g f x).1.linearIndependent }
  spans := by
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    exact fun x ↦ (positiveRootFrameSection_properties I g f x).2.1

/-- The actual metric duals of the normalized fields, as smooth dual-bundle sections. -/
def positiveRootDualSection
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (i : Fin n) :
    ContMDiffSection I (E →L[ℝ] ℝ) ∞
      (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) where
  toFun x := g.inner x (positiveRootFrameSection I g f i x)
  contMDiff_toFun := g.contMDiff.clm_bundle_apply (positiveRootFrameSection I g f i).contMDiff

/-- The normalized orthonormal basis in an actual metric tangent fiber. -/
def positiveRootOrthonormalBasis
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact OrthonormalBasis.mk (positiveRootFrameSection_properties I g f x).1
    (le_of_eq (positiveRootFrameSection_properties I g f x).2.1.symm)

/-- The actual Euclidean coframe, represented without changing the original
topological vector space structure on the tangent fibers. -/
def positiveRootCoframe
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact (positiveRootOrthonormalBasis I g f x).repr.toLinearEquiv

/-- Coframe coordinates are exactly the constructed smooth metric dual sections. -/
theorem positiveRootCoframe_apply_eq_dual
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) (v : TangentSpace I x) (i : Fin n) :
    positiveRootCoframe I g f x v i = positiveRootDualSection I g f i x v := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  change (positiveRootOrthonormalBasis I g f x).repr v i = _
  rw [OrthonormalBasis.repr_apply_apply]
  simp only [positiveRootOrthonormalBasis, OrthonormalBasis.coe_mk]
  rfl

/-- The full coframe is a fiberwise isometry for precisely the input metric. -/
theorem positiveRootCoframe_isometry
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) (v w : TangentSpace I x) :
    inner ℝ (positiveRootCoframe I g f x v) (positiveRootCoframe I g f x w) =
      g.inner x v w := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact (positiveRootOrthonormalBasis I g f x).repr.inner_map_map v w

/-- The normalized frame is dual to the smooth coframe. -/
theorem positiveRootCoframe_on_normalizedFrame
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) (i j : Fin n) :
    positiveRootCoframe I g f x (positiveRootFrameSection I g f j x) i =
      if i = j then 1 else 0 := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [positiveRootCoframe_apply_eq_dual]
  exact orthonormal_iff_ite.mp (positiveRootFrameSection_properties I g f x).1 i j

/-- The basis underlying the original full frame, used to state the paper's
formula relative to the original dual trivialization. -/
def fullFrameBasis (f : FullTangentFrame I (M := M) n) (x : M) :
    Module.Basis (Fin n) ℝ (TangentSpace I x) :=
  Module.Basis.mk (f.framed.independent x) (le_of_eq (f.spans x).symm)

private theorem positiveRootDualSection_on_originalFrame
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) (i j : Fin n) :
    positiveRootDualSection I g f i x (f.framed.frame j x) =
      fullFrameGramRoot I g f x i j := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [← (positiveRootFrameSection_properties I g f x).2.2 j]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, ← positiveRootCoframe_apply_eq_dual,
    positiveRootCoframe_on_normalizedFrame]
  simp

/-- The literal positive-root coframe formula `theta = P eta`, where `eta` is
the dual of the original frame. This also fixes the matrix transpose convention. -/
theorem positiveRootCoframe_formula
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (x : M) (v : TangentSpace I x) (i : Fin n) :
    positiveRootCoframe I g f x v i = ∑ j, fullFrameGramRoot I g f x i j *
      (fullFrameBasis I f x).equivFun v j := by
  rw [positiveRootCoframe_apply_eq_dual]
  conv_lhs => rw [← (fullFrameBasis I f x).sum_equivFun v]
  simp only [map_sum, map_smul, smul_eq_mul, fullFrameBasis, Module.Basis.coe_mk,
    positiveRootDualSection_on_originalFrame]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Smooth coframe normalization with the paper's explicit positive-root formula.
The input is only an actual smooth full tangent frame and actual smooth positive
metric. The output contains smooth covectors, a full smooth dual tangent frame,
and actual fiberwise Euclidean isomorphisms preserving exactly that metric.

Proof: evaluate the metric on the given frame, apply smooth positive-root
calculus on the symmetric matrix space, and form the inverse-root column sums.
The accepted matrix normalization theorem gives orthonormality and full span in
each metric tangent fiber. Pairing with the metric gives smooth covectors; the
orthonormal-basis representation proves their isometry and inverse properties.
Reconstruction proves `theta=P eta`. All constructions include empty manifolds,
zero-dimensional fibers and disconnected manifolds, without compactness.
Source: `prop:initialization`, positive metric-root normalization, line 798. -/
theorem smooth_coframe_normalization
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) :
    ∃ (e : FullTangentFrame I (M := M) n)
      (θ : ∀ x : M, TangentSpace I x ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
      (coframe : Fin n → ContMDiffSection I (E →L[ℝ] ℝ) ∞
        (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)),
      (∀ x v i, θ x v i = coframe i x v) ∧
      (∀ x v w, inner ℝ (θ x v) (θ x w) = g.inner x v w) ∧
      (∀ x i j, θ x (e.framed.frame j x) i = if i = j then 1 else 0) ∧
      (∀ x v i, θ x v i = ∑ j, fullFrameGramRoot I g f x i j *
        (fullFrameBasis I f x).equivFun v j) ∧
      (∀ x i, e.framed.frame i x = ∑ j, (fullFrameGramRoot I g f x)⁻¹ j i •
        f.framed.frame j x) := by
  refine ⟨positiveRootFullFrame I g f, positiveRootCoframe I g f,
    positiveRootDualSection I g f, positiveRootCoframe_apply_eq_dual I g f,
    positiveRootCoframe_isometry I g f, positiveRootCoframe_on_normalizedFrame I g f,
    positiveRootCoframe_formula I g f, ?_⟩
  exact fun _ _ ↦ rfl

#print axioms smooth_coframe_normalization
#print axioms positiveRootDualSection
#print axioms positiveRootFullFrame
#print axioms positiveRootCoframe_formula
#print axioms positiveRootCoframe_isometry
#print axioms positiveRootFrameSection_properties

end GlobalEmbedding.Paper
