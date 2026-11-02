import GlobalEmbedding.Paper.SymmetricBilinearDescendEvaluation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# The original once-sorted coordinate products in the binary symmetric quotient

Source: `main.tex`, lem:increments620–629, actual transverse beta coordinates.
W2 only the required coordinate independence; no new quotient, norm or basis carrier.
-/

noncomputable section
namespace GlobalEmbedding.Paper

/-- Once-sorted coordinate products are independent in the ORIGINAL binary
symmetric quotient. Descend each actual symmetric coordinate bilinear functional
using the accepted descent theorem. Its value is one on its off-diagonal product
and two on its diagonal product, and zero on all other once-sorted products.
Apply it to an actual linear relation and cancel the nonzero scalar. This uses
exactly the original quotient normalization, including m=0 and all diagonals.
Source: the independent transverse coordinates of actual beta in(6.2). -/
theorem increments_symmetric_coordinate_products_linearIndependent (m : ℕ) :
    LinearIndependent ℝ
      (fun ij : {p : Fin m × Fin m // p.1 ≤ p.2} ↦
        symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace.single ij.val.1 1) (EuclideanSpace.single ij.val.2 1)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc ij
  let β : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun v w ↦ v ij.val.1 * w ij.val.2 + v ij.val.2 * w ij.val.1)
      (by intro v v' w; simp; ring)
      (by intro r v w; simp; ring)
      (by intro v w w'; simp; ring)
      (by intro r v w; simp; ring)
  have hβ (v w : EuclideanSpace ℝ (Fin m)) : β v w = β w v := by
    change v ij.val.1 * w ij.val.2 + v ij.val.2 * w ij.val.1 = _
    change _ = w ij.val.1 * v ij.val.2 + w ij.val.2 * v ij.val.1
    ring
  let L := symmetricBilinearDescend β hβ
  have heval (q : {p : Fin m × Fin m // p.1 ≤ p.2}) :
      L (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace.single q.val.1 1) (EuclideanSpace.single q.val.2 1)) =
      if q = ij then (if ij.val.1 = ij.val.2 then (2 : ℝ) else 1) else 0 := by
    change β (EuclideanSpace.single q.val.1 1) (EuclideanSpace.single q.val.2 1) = _
    by_cases he : q = ij
    · subst q
      by_cases hd : ij.val.1 = ij.val.2
      · simp [β, hd]
        norm_num
      · simp [β, hd, eq_comm]
    · have hf : ¬(q.val.1 = ij.val.1 ∧ q.val.2 = ij.val.2) := by
        rintro ⟨h₁, h₂⟩
        exact he (Subtype.ext (Prod.ext h₁ h₂))
      have hr : ¬(q.val.1 = ij.val.2 ∧ q.val.2 = ij.val.1) := by
        rintro ⟨h₁, h₂⟩
        have hq := q.property
        have hi := ij.property
        apply he
        apply Subtype.ext
        apply Prod.ext <;> omega
      by_cases h₁ : q.val.1 = ij.val.1 <;>
        by_cases h₂ : q.val.2 = ij.val.2 <;>
        by_cases h₃ : q.val.1 = ij.val.2 <;>
        by_cases h₄ : q.val.2 = ij.val.1 <;>
        simp_all [β, PiLp.single_apply, eq_comm]
  have h := congrArg (fun z ↦ L z) hc
  simp only [map_sum, map_smul, map_zero] at h
  simp_rw [heval] at h
  simp only [smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h
  split_ifs at h <;> linarith

end GlobalEmbedding.Paper
