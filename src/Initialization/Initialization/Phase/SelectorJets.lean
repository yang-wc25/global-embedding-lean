import Initialization.Phase.GramFrame
import Initialization.Phase.CoordinateHyperplane
import GlobalEmbedding.Paper.WholeProductSelectorFromCollar
import GlobalEmbedding.Paper.SymmetricSquareMapProduct
import GlobalEmbedding.Offline.ActualHessianJet

/-!
# Actual first and second jets of the fixed selector orbit

The ideal model at a sphere-product point is its genuine multi-orbit leaf.
The first jet is the linear extension of the actual Hopf derivative columns;
the second is the already established native coordinate Hessian lift on the
project's original symmetric-square quotient.  Neither is an independent
formal tensor supplied to phase stability.
-/

noncomputable section

open Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Initialization

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance selectorJetRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance selectorJetSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)


section OrbitJets

variable {n N : ℕ} (C : Fin n → ℕ) [∀ i, Fact (0 < C i)]
  (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))

/-- The literal ideal first jet, with columns equal to the actual Hopf derivatives. -/
def selectorIdealFirstJet (z : FreeHopfProduct C) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  gramFrame (fun i ↦ freeHopfDeriv C i S z)

/-- The literal ideal second jet is the actual Hessian of the selector's
genuine orbit leaf, using the existing canonical quotient lift. -/
def selectorIdealSecondJet (z : FreeHopfProduct C) :
    SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  coordinateHessianJet (S ∘ freeHopfOrbitLift C z) 0

variable (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)

include hS

/-- The column-defined ideal first jet is Lean's actual derivative of the
same native orbit leaf. -/
theorem selectorIdealFirstJet_eq_fderiv (z : FreeHopfProduct C) :
    selectorIdealFirstJet C S z = fderiv ℝ (S ∘ freeHopfOrbitLift C z) 0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe, selectorIdealFirstJet, gramFrame_single]
  have h := freeHopf_first_orbitLift C S hS z 0 i
  rw [freeHopfOrbitLift_zero] at h
  exact (freeHopfGenerator_mvfderiv C i S hS z).symm.trans h

/-- Every actual Hessian column is precisely the corresponding ordered
Hopf second derivative, with the original period-one normalization. -/
theorem selectorIdealSecondJet_basis_product (z : FreeHopfProduct C) (i j : Fin n) :
    selectorIdealSecondJet C S z
      (symmetricSquareProduct (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      freeHopfDeriv C i (freeHopfDeriv C j S) z := by
  have hL : ContDiff ℝ ∞ (S ∘ freeHopfOrbitLift C z) :=
    (hS.comp (freeHopfOrbitLift_contMDiff C z)).contDiff
  have hs (k : Fin n) : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (freeHopfDeriv C k S) :=
    contMDiff_orbitDeriv (freeHopfProductFlow C k)
      (freeHopfProductFlow_contMDiff C k) S hS
  have he (k : Fin n) : balancedDirectionalDerivative S (freeHopfGenerator C k) =
      freeHopfDeriv C k S :=
    funext (fun x ↦ freeHopfGenerator_mvfderiv C k S hS x)
  have hsecond := freeHopf_second_orbitLift C S hS z 0 i j
  rw [freeHopfOrbitLift_zero, he j] at hsecond
  change mvfderiv (freeHopfModel C) (freeHopfDeriv C j S) z
      (freeHopfGenerator C i z) = _ at hsecond
  rw [freeHopfGenerator_mvfderiv C i _ (hs j)] at hsecond
  have hdf : DifferentiableAt ℝ (fderiv ℝ (S ∘ freeHopfOrbitLift C z)) 0 :=
    (hL.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  have heval : fderiv ℝ (fun y ↦ fderiv ℝ (S ∘ freeHopfOrbitLift C z) y
      (EuclideanSpace.single j 1)) 0 =
      (fderiv ℝ (fderiv ℝ (S ∘ freeHopfOrbitLift C z)) 0).flip
        (EuclideanSpace.single j 1) := by
    have h := hdf.hasFDerivAt.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single j 1) (0 : EuclideanSpace ℝ (Fin n)))
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using h.fderiv
  rw [heval] at hsecond
  rw [selectorIdealSecondJet,
    coordinateHessianJet_product (hL.contDiffAt.of_le (by simp))]
  exact hsecond.symm

/-- The literal Hessian of the same orbit leaf already takes values in the
partial normal space.  The full product's total normal is not used. -/
theorem selectorIdealSecondJet_normal
    (hGram : ∀ z, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S z) = 1)
    (z : FreeHopfProduct C) :
    (LinearMap.range (selectorIdealFirstJet C S z).toLinearMap)ᗮ.starProjection.comp
      (selectorIdealSecondJet C S z) = selectorIdealSecondJet C S z := by
  apply ContinuousLinearMap.coe_injective
  apply selector_symSquare_ext_basis
  intro i j
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  rw [selectorIdealSecondJet_basis_product C S hS]
  apply Submodule.starProjection_eq_self_iff.mpr
  rw [selectorIdealFirstJet, gramFrame_range]
  have h := selector_second_mem_orbitLeaf_normalSpace C S hS hGram z i j
  rwa [selector_orbitLeaf_normalSpace C S hS z] at h

/-- Smoothness of the actual selector supplies continuity of every second
column and hence of the whole canonical quotient Hessian operator. -/
theorem selectorIdealSecondJet_continuous :
    Continuous (selectorIdealSecondJet C S) := by
  apply continuous_clm_apply.mpr
  have hs (i : Fin n) : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (freeHopfDeriv C i S) :=
    contMDiff_orbitDeriv (freeHopfProductFlow C i) (freeHopfProductFlow_contMDiff C i) S hS
  have hcol (i j : Fin n) : Continuous (fun z ↦ selectorIdealSecondJet C S z
      (symmetricSquareProduct (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) := by
    have he : (fun z ↦ selectorIdealSecondJet C S z
        (symmetricSquareProduct (EuclideanSpace ℝ (Fin n))
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) =
        fun z ↦ freeHopfDeriv C i (freeHopfDeriv C j S) z :=
      funext (fun z ↦ selectorIdealSecondJet_basis_product C S hS z i j)
    rw [he]
    exact (contMDiff_orbitDeriv (freeHopfProductFlow C i)
      (freeHopfProductFlow_contMDiff C i) _ (hs j)).continuous
  intro u
  refine Submodule.Quotient.induction_on _ u (fun z ↦ ?_)
  change Continuous (fun x ↦ selectorIdealSecondJet C S x
    (symmetricSquareQuotient (EuclideanSpace ℝ (Fin n)) z))
  induction z using TensorProduct.inductionOn with
  | tmul v w =>
    change Continuous (fun x ↦ selectorIdealSecondJet C S x
      (symmetricSquareProduct (EuclideanSpace ℝ (Fin n)) v w))
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    rw [← b.sum_repr v, ← b.sum_repr w]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    apply continuous_finsetSum
    intro i _
    apply Continuous.fun_const_smul
    apply continuous_finsetSum
    intro j _
    apply Continuous.fun_const_smul
    simpa only [b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hcol j i
  | add z w hz hw => simpa only [map_add] using hz.fun_add hw

/-- One bound for the literal selector Hessian is fixed on the whole sphere
product before the source charts or any initialization frequency is chosen. -/
theorem selectorIdealSecondJet_uniform_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ z, ‖selectorIdealSecondJet C S z‖ ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (selectorIdealSecondJet_continuous C S hS).continuousOn
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun z ↦ ?_⟩
  exact (hB z (Set.mem_univ z)).trans (le_max_right _ _)

end OrbitJets

section OldCoordinates

variable {m N : ℕ} (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]
  (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
  (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)

/-- Restricting the genuine orbit Hessian to the actual old coordinates
recovers the original selector theorem's true second form exactly. -/
theorem selectorIdealSecondJet_oldCoordinates
    (hGram : ∀ z, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S z) = 1)
    (z : FreeHopfProduct C) :
    (selectorIdealSecondJet C S z).comp (symmetricSquareMapL (oldCoordinateInjection m)) =
      (selectorOldSecondForm C S hS z).toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  apply selector_symSquare_ext_basis
  intro i j
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    symmetricSquareMapL_product, oldCoordinateInjection_single,
    LinearMap.coe_toContinuousLinearMap]
  rw [selectorIdealSecondJet_basis_product C S hS,
    selectorOldSecondForm_basis_product C S hS hGram]

end OldCoordinates

end GlobalEmbedding.Initialization
