import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The actual oriented cofactor of an ordered codimension-one Euclidean frame

Source: `main.tex`, `thm:free`, lines 421–495. DAG: `free-ordered-cofactor`.
The standard Euclidean determinant is contracted in its last slot and represented
by the real Riesz isometry. This is a polynomial construction on actual columns;
its normalization requires only their actual linear independence.
-/

noncomputable section

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

abbrev FreeCofactorSpace (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

private instance freeCofactorSpace_finrank (d : ℕ) :
    Fact (Module.finrank ℝ (FreeCofactorSpace d) = d + 1) := ⟨by simp [FreeCofactorSpace]⟩

/-- The standard positively oriented Euclidean volume, with actual ordered slots. -/
def freeOrderedVolume (d : ℕ) :
    (FreeCofactorSpace d) [⋀^Fin (d + 1)]→L[ℝ] ℝ :=
  { (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis.det with
    cont := by
      change Continuous (fun v ↦
        Matrix.det ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis.toMatrix v))
      apply Continuous.matrix_det
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (EuclideanSpace.proj i).continuous.comp (continuous_apply j) }

/-- This determinant is exactly the volume form of the standard Euclidean orientation.
Proof: use Mathlib's volume-form identity for the standard orthonormal basis. -/
theorem freeOrderedVolume_eq_volumeForm (d : ℕ) :
    (freeOrderedVolume d).toAlternatingMap =
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis.orientation.volumeForm := by
  exact (Orientation.volumeForm_robust _
    (EuclideanSpace.basisFun (Fin (d + 1)) ℝ) rfl).symm

/-- The actual cofactor is the Riesz representative of last-slot volume contraction. -/
def freeOrderedCofactor (d : ℕ) (v : Fin d → FreeCofactorSpace d) : FreeCofactorSpace d :=
  (InnerProductSpace.toDual ℝ (FreeCofactorSpace d)).symm
    ((freeOrderedVolume d).toContinuousMultilinearMap.curryRight v)

/-- Contraction against a final column is exactly the ordered determinant.
Proof: apply the Riesz identity and the right-currying evaluation formula. -/
theorem freeOrderedCofactor_inner (d : ℕ) (v : Fin d → FreeCofactorSpace d)
    (w : FreeCofactorSpace d) :
    inner ℝ (freeOrderedCofactor d v) w = freeOrderedVolume d (Fin.snoc v w) := by
  exact InnerProductSpace.toDual_symm_apply

/-- Every actual input column is perpendicular to its cofactor.
Proof: the contracted determinant has two equal columns. -/
theorem freeOrderedCofactor_orthogonal (d : ℕ) (v : Fin d → FreeCofactorSpace d)
    (i : Fin d) : inner ℝ (freeOrderedCofactor d v) (v i) = 0 := by
  rw [freeOrderedCofactor_inner]
  exact (freeOrderedVolume d).map_eq_zero_of_eq (Fin.snoc v (v i))
    (by simp) (Fin.castSucc_ne_last i)

/-- Actual independence forces the cofactor to be nonzero.
Proof: extend the ordered family by one independent column. Its determinant
is a unit, whereas a zero Riesz vector would make that determinant vanish. -/
theorem freeOrderedCofactor_ne_zero (d : ℕ) (v : Fin d → FreeCofactorSpace d)
    (hv : LinearIndependent ℝ v) : freeOrderedCofactor d v ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_linearIndependent_snoc_of_lt_finrank hv
    (by simp [FreeCofactorSpace])
  have hspan := hw.span_eq_top_of_card_eq_finrank' (by simp [FreeCofactorSpace])
  have hdet := ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis.is_basis_iff_det).mp
    ⟨hw, hspan⟩
  intro hzero
  have hinner := freeOrderedCofactor_inner d v w
  rw [hzero, inner_zero_left] at hinner
  exact hdet.ne_zero hinner.symm

/-- The positively oriented unit complement of the actual ordered columns. -/
def freeOrderedUnitComplement (d : ℕ) (v : Fin d → FreeCofactorSpace d) :
    FreeCofactorSpace d := ‖freeOrderedCofactor d v‖⁻¹ • freeOrderedCofactor d v

/-- The actual normalized cofactor has unit norm and is orthogonal to every column.
Proof: normalize the nonzero cofactor and use real bilinearity of the inner product. -/
theorem freeOrderedUnitComplement_spec (d : ℕ) (v : Fin d → FreeCofactorSpace d)
    (hv : LinearIndependent ℝ v) :
    ‖freeOrderedUnitComplement d v‖ = 1 ∧
      ∀ i, inner ℝ (freeOrderedUnitComplement d v) (v i) = 0 := by
  constructor
  · exact NormedSpace.norm_normalize (freeOrderedCofactor_ne_zero d v hv)
  · intro i
    simp [freeOrderedUnitComplement, inner_smul_left, freeOrderedCofactor_orthogonal]

/-- The normalized complement retains the positive last-slot orientation.
Proof: last-slot volume is the inner product with the cofactor, hence equals
its squared norm divided by its nonzero norm. -/
theorem freeOrderedUnitComplement_volume (d : ℕ) (v : Fin d → FreeCofactorSpace d)
    (hv : LinearIndependent ℝ v) :
    freeOrderedVolume d (Fin.snoc v (freeOrderedUnitComplement d v)) =
      ‖freeOrderedCofactor d v‖ := by
  rw [← freeOrderedCofactor_inner, freeOrderedUnitComplement, inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hn := norm_ne_zero_iff.mpr (freeOrderedCofactor_ne_zero d v hv)
  change ‖freeOrderedCofactor d v‖⁻¹ * ‖freeOrderedCofactor d v‖ ^ 2 = _
  field_simp

/-- Appending the actual normalized cofactor completes the actual ordered basis.
Proof: its ordered determinant is strictly positive, hence a unit; apply
Mathlib's exact determinant characterization of a basis. -/
theorem freeOrderedUnitComplement_linearIndependent (d : ℕ)
    (v : Fin d → FreeCofactorSpace d) (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ (Fin.snoc v (freeOrderedUnitComplement d v)) := by
  apply (((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis.is_basis_iff_det).mpr ?_).1
  apply isUnit_iff_ne_zero.mpr
  change freeOrderedVolume d (Fin.snoc v (freeOrderedUnitComplement d v)) ≠ 0
  rw [freeOrderedUnitComplement_volume d v hv]
  exact norm_ne_zero_iff.mpr (freeOrderedCofactor_ne_zero d v hv)

section Smooth

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)

/-- The actual unnormalized cofactor is native smooth in every smooth ordered family.
Proof: right-curried continuous volume is a continuous multilinear polynomial,
and the inverse real Riesz isometry is continuous linear. -/
theorem freeOrderedCofactor_contMDiff (d : ℕ) {v : M → Fin d → FreeCofactorSpace d}
    (hv : ∀ i, ContMDiff I 𝓘(ℝ, FreeCofactorSpace d) ∞ (fun x ↦ v x i)) :
    ContMDiff I 𝓘(ℝ, FreeCofactorSpace d) ∞ (fun x ↦ freeOrderedCofactor d (v x)) := by
  let R : StrongDual ℝ (FreeCofactorSpace d) →L[ℝ] FreeCofactorSpace d :=
    (InnerProductSpace.toDual ℝ (FreeCofactorSpace d)).symm.toLinearIsometry.toContinuousLinearMap
  apply R.contMDiff.comp
  exact ((freeOrderedVolume d).toContinuousMultilinearMap.curryRight.contDiff.contMDiff).comp
    (contMDiff_pi_module_iff.mpr hv)

/-- Normalization gives a genuine global native smooth unit complement.
Proof: the actual cofactor is nowhere zero, so its norm and reciprocal norm
are smooth; multiply the polynomial cofactor by this actual reciprocal norm. -/
theorem freeOrderedUnitComplement_contMDiff (d : ℕ)
    {v : M → Fin d → FreeCofactorSpace d}
    (hv : ∀ i, ContMDiff I 𝓘(ℝ, FreeCofactorSpace d) ∞ (fun x ↦ v x i))
    (hind : ∀ x, LinearIndependent ℝ (v x)) :
    ContMDiff I 𝓘(ℝ, FreeCofactorSpace d) ∞
      (fun x ↦ freeOrderedUnitComplement d (v x)) := by
  have hc := freeOrderedCofactor_contMDiff I d hv
  have hn : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ ‖freeOrderedCofactor d (v x)‖) := by
    intro x
    exact (contDiffAt_norm ℝ (freeOrderedCofactor_ne_zero d (v x) (hind x))).comp_contMDiffAt
      (f := fun y : M ↦ freeOrderedCofactor d (v y)) (hc x)
  exact (hn.inv₀ (fun x ↦ norm_ne_zero_iff.mpr
    (freeOrderedCofactor_ne_zero d (v x) (hind x)))).smul hc

/-- Actual ordered smooth independent columns supply a global smooth unit normal.
Proof: choose the actual normalized Riesz cofactor, whose smoothness and all
pointwise identities were proved above. No global normal is supplied as input. -/
theorem exists_freeOrderedUnitComplement (d : ℕ)
    {v : M → Fin d → FreeCofactorSpace d}
    (hv : ∀ i, ContMDiff I 𝓘(ℝ, FreeCofactorSpace d) ∞ (fun x ↦ v x i))
    (hind : ∀ x, LinearIndependent ℝ (v x)) :
    ∃ ν : M → FreeCofactorSpace d,
      ContMDiff I 𝓘(ℝ, FreeCofactorSpace d) ∞ ν ∧
      (∀ x, ‖ν x‖ = 1) ∧ (∀ x i, inner ℝ (ν x) (v x i) = 0) ∧
      (∀ x, 0 < freeOrderedVolume d (Fin.snoc (v x) (ν x))) := by
  refine ⟨fun x ↦ freeOrderedUnitComplement d (v x),
    freeOrderedUnitComplement_contMDiff I d hv hind, ?_, ?_, ?_⟩
  · exact fun x ↦ (freeOrderedUnitComplement_spec d (v x) (hind x)).1
  · exact fun x ↦ (freeOrderedUnitComplement_spec d (v x) (hind x)).2
  · intro x
    rw [freeOrderedUnitComplement_volume d (v x) (hind x)]
    exact norm_pos_iff.mpr (freeOrderedCofactor_ne_zero d (v x) (hind x))

end Smooth

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeOrderedVolume
#print axioms GlobalEmbedding.Paper.freeOrderedVolume_eq_volumeForm
#print axioms GlobalEmbedding.Paper.freeOrderedCofactor
#print axioms GlobalEmbedding.Paper.freeOrderedCofactor_inner
#print axioms GlobalEmbedding.Paper.freeOrderedCofactor_orthogonal
#print axioms GlobalEmbedding.Paper.freeOrderedCofactor_ne_zero
#print axioms GlobalEmbedding.Paper.freeOrderedUnitComplement_spec
#print axioms GlobalEmbedding.Paper.freeOrderedUnitComplement_volume
#print axioms GlobalEmbedding.Paper.freeOrderedUnitComplement_linearIndependent
#print axioms GlobalEmbedding.Paper.freeOrderedCofactor_contMDiff
#print axioms GlobalEmbedding.Paper.freeOrderedUnitComplement_contMDiff
#print axioms GlobalEmbedding.Paper.exists_freeOrderedUnitComplement
