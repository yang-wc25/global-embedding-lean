import GlobalEmbedding.Paper.SupportedKernelRadicalEquations
import GlobalEmbedding.Paper.LinearSecondFormOperatorOpen
import GlobalEmbedding.Paper.SupportedRankNormalDirectionCount
import GlobalEmbedding.Paper.SupportedRadicalDerivativeFactorization
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import GlobalEmbedding.Paper.SupportedRadicalGoodRowBlock
import GlobalEmbedding.Paper.SymmetricSquareHilbertPairing
import GlobalEmbedding.Paper.SupportedRadicalEvaluationLift
import GlobalEmbedding.Paper.SupportedRadicalMixedKernelBound
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Actual local geometry of the original supported-kernel locus

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1012 and 1018–1029. This parent consumer keeps the original symmetric quotient,
its original Hilbert norm, the actual kernel graph, and one common defining equation.
-/

noncomputable section
open scoped ContDiff TensorProduct
namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
attribute [local instance] operatorSelfAdjointContinuousSMul

local instance supportedGeometrySquareInner : InnerProductSpace ℝ (SymmetricSquare V) :=
  { Submodule.instQuotientInnerProductSpace (symmetricSquareRelations V) with
    toNormedSpace := squareNS V }

/-- The GENUINE orthogonal projection to the actual mixed subspace inside H preserves
original operator evaluation at e. Proof: the removed vector is perpendicular to every
original product e⊙v; the original quotient pairing makes its evaluation at e zero.
Source: `prop:supported-rank`, actual mixed projection of the kernel derivative. -/
theorem supportedKernel_mixed_projection_evaluation
    (H : Submodule ℝ (SymmetricSquare V)) (e : V)
    (hZ : LinearMap.range (symmetricSquareProduct V e) ≤ H) (q : H) :
    (symmetricSquareToSelfAdjoint
      (((LinearMap.range (symmetricSquareProduct V e)).comap H.subtype).starProjection q :
        SymmetricSquare V)).val e =
      (symmetricSquareToSelfAdjoint (q : SymmetricSquare V)).val e := by
  let Z : Submodule ℝ H := (LinearMap.range (symmetricSquareProduct V e)).comap H.subtype
  let z : H := q - Z.starProjection q
  have hz : z ∈ Zᗮ := Z.sub_starProjection_mem_orthogonal q
  have heval : (symmetricSquareToSelfAdjoint (z : SymmetricSquare V)).val e = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    let v := (symmetricSquareToSelfAdjoint (z : SymmetricSquare V)).val e
    let p : H := ⟨symmetricSquareProduct V e v, hZ ⟨v, rfl⟩⟩
    have hp : p ∈ Z := ⟨v, rfl⟩
    have hi : inner ℝ z p = 0 := Z.inner_left_of_mem_orthogonal hp hz
    change inner ℝ (z : SymmetricSquare V) (symmetricSquareProduct V e v) = 0 at hi
    rw [symmetricSquare_inner_product_eq_operator] at hi
    exact hi
  change (symmetricSquareToSelfAdjoint
    ((q : SymmetricSquare V) - (Z.starProjection q : SymmetricSquare V))).val e = 0 at heval
  rw [map_sub] at heval
  change (symmetricSquareToSelfAdjoint (q : SymmetricSquare V)).val e -
    (symmetricSquareToSelfAdjoint (Z.starProjection q : SymmetricSquare V)).val e = 0 at heval
  exact (sub_eq_zero.mp heval).symm

/-- The same genuine mixed projection preserves the actual coordinate evaluation used
by the SAME scalar-row residual. No invariant-subspace assumption about G is involved.
Source: `prop:supported-rank`, actual normal-equation factorization. -/
theorem supportedKernel_mixed_projection_coordinate_evaluation
    (H : Submodule ℝ (SymmetricSquare V)) (U : Submodule ℝ V)
    (d : (ℝ × U) ≃L[ℝ] V) (e : V) (hde : d (1, 0) = e)
    (hZ : LinearMap.range (symmetricSquareProduct V e) ≤ H) (q : H) :
    supportedRadicalCoordinateOperatorMap U d
        (((LinearMap.range (symmetricSquareProduct V e)).comap H.subtype).starProjection q)
        (1, 0) = supportedRadicalCoordinateOperatorMap U d (q : SymmetricSquare V) (1, 0) := by
  apply d.injective
  rw [supportedRadicalCoordinateOperatorMap_apply,
    supportedRadicalCoordinateOperatorMap_apply, hde,
    supportedKernel_mixed_projection_evaluation H e hZ q]

/-- A genuine original tensor lift to the actual kernel complement, in fixed coordinates.
Source: `prop:supported-rank`, true local normal-submersion realization. -/
def supportedKernelRadicalLift (K : Submodule ℝ (SymmetricSquare V))
    (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V) (e : V) :
    (ℝ × U) →L[ℝ] Kᗮ :=
  Kᗮ.orthogonalProjectionOnto.comp
    ((supportedRadicalEvaluationLift e).toContinuousLinearMap.comp (d : (ℝ × U) →L[ℝ] V))

/-- The actual complement lift realizes every original operator evaluation at the radical.
Only true common-radical annihilation and the original unit normalization are required.
Source: `prop:supported-rank`, actual symmetric-kernel variation realization. -/
theorem supportedKernelRadicalLift_evaluation
    (K : Submodule ℝ (SymmetricSquare V)) (U : Submodule ℝ V)
    (d : (ℝ × U) ≃L[ℝ] V) (e : V) (he : ‖e‖ = 1) (hde : d (1, 0) = e)
    (hK : ∀ q ∈ K, (symmetricSquareToSelfAdjoint q).val e = 0) (v : ℝ × U) :
    supportedRadicalCoordinateOperatorMap U d (supportedKernelRadicalLift K U d e v)
      (1, 0) = v := by
  let E : SymmetricSquare V →ₗ[ℝ] V := contractionKernelQuotientMap (innerₗ V e)
  have hE : ∀ v' : V, E (supportedRadicalEvaluationLift e v') = v' := by
    intro v'
    rw [← symmetricSquareToSelfAdjoint_apply]
    exact supportedRadicalEvaluationLift_apply e he v'
  have hkill : ∀ q ∈ K, E q = 0 := by
    intro q hq
    rw [← symmetricSquareToSelfAdjoint_apply]
    exact hK q hq
  have h := supportedRadicalComplement_evaluation_lift K E
    (supportedRadicalEvaluationLift e) hkill hE (d v)
  apply d.injective
  rw [supportedRadicalCoordinateOperatorMap_apply, hde]
  rw [symmetricSquareToSelfAdjoint_apply]
  exact h

/-- The SAME residual restricted to the ACTUAL original symmetric-kernel variations has
surjective derivative. The genuine tensor lift supplies the variations; full arbitrary
operator-family surjectivity is not substituted. Source: `prop:supported-rank`, local
normal submersion before composition with the actual onto kernel map. -/
theorem supportedKernelRadicalMixed_fderiv_surjective
    (K : Submodule ℝ (SymmetricSquare V)) (U : Submodule ℝ V)
    (d : (ℝ × U) ≃L[ℝ] V) (e : V) (he : ‖e‖ = 1) (hde : d (1, 0) = e)
    (hK : ∀ q ∈ K, (symmetricSquareToSelfAdjoint q).val e = 0)
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (f : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (f : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r Q) = 0) :
    Function.Surjective (fderiv ℝ (supportedRadicalMixedEquation a r w hw Q
      ((supportedRadicalCoordinateOperatorMap U d).comp Kᗮ.subtypeL)) 0) := by
  intro T
  let J := (supportedRadicalCoordinateOperatorMap U d).comp Kᗮ.subtypeL
  let Y : K →L[ℝ] Kᗮ :=
    (supportedKernelRadicalLift K U d e).comp (r.ker.subtypeL.comp T)
  have heval (k : K) : J (Y k) (1, 0) = (T k : ℝ × U) :=
    supportedKernelRadicalLift_evaluation K U d e he hde hK (T k)
  have hrows : supportedRadicalRows a r (J.comp Y) (1, 0) = 0 := by
    apply a.injective
    apply ContinuousLinearMap.ext
    intro k
    rw [supportedRadicalRows_apply]
    simp only [map_zero, zero_apply]
    change r (J (Y k) (1, 0)) = 0
    rw [heval k]
    exact (T k).property
  refine ⟨Y, ?_⟩
  apply ContinuousLinearMap.ext
  intro k
  apply Subtype.ext
  rw [supportedRadicalMixedEquation_fderiv_apply a r w hw Q f hA hC J Y k, hrows]
  simp only [map_zero, neg_zero, heval k]
  change (T k : ℝ × U) + (Q k) (0 : ℝ × U) = (T k : ℝ × U)
  rw [(Q k).map_zero, add_zero]

/-- The actual mixed restriction of the SAME derivative loses at most dim U directions.
The required evaluation injection is discharged by the sole original mixed tensor theorem,
not supplied as an original target assumption. Source: `prop:supported-rank`, support loss. -/
theorem supportedKernelRadicalMixed_kernel_finrank_le
    (K : Submodule ℝ (SymmetricSquare V)) (U : Submodule ℝ V)
    (d : (ℝ × U) ≃L[ℝ] V) (e : V) (he : inner ℝ e e = 1) (hde : d (1, 0) = e)
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (f : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (f : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r Q) = 0) :
    Module.finrank ℝ (fderiv ℝ (supportedRadicalMixedEquation a r w hw Q
      ((supportedRadicalCoordinateOperatorMap U d).comp (Kᗮ.subtypeL.comp
        ((LinearMap.range (symmetricSquareProduct V e)).comap Kᗮ.subtype).subtypeL))) 0).ker ≤
      Module.finrank ℝ U := by
  apply supportedRadicalMixedEquation_kernel_finrank_le a r w hw Q f hA hC
  intro x y h
  have hx : ((x : Kᗮ) : SymmetricSquare V) ∈
      LinearMap.range (symmetricSquareProduct V e) := x.property
  have hy : ((y : Kᗮ) : SymmetricSquare V) ∈
      LinearMap.range (symmetricSquareProduct V e) := y.property
  have hxy : (⟨((x : Kᗮ) : SymmetricSquare V), hx⟩ :
      LinearMap.range (symmetricSquareProduct V e)) = ⟨((y : Kᗮ) : SymmetricSquare V), hy⟩ :=
    supportedRadicalMixedCoordinate_evaluation_injective U d e he hde h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : LinearMap.range (symmetricSquareProduct V e) ↦
    (q : SymmetricSquare V)) hxy

/-- The two already proved actual derivative formulas coincide on each affine variation.
This is a reuse adapter, with no second differentiation. Source: `prop:supported-rank`. -/
theorem supportedKernelRadicalMixed_fderiv_eq_normal
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (K : Submodule ℝ (SymmetricSquare V)) (U : Submodule ℝ V)
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (f : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (f : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r Q) = 0)
    (J : Z →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (Y : K →L[ℝ] Z) :
    fderiv ℝ (supportedRadicalMixedEquation a r w hw Q J) 0 Y =
      fderiv ℝ (supportedRadicalNormalResidual a r w hw) Q (J.comp Y) := by
  apply ContinuousLinearMap.ext
  intro k
  apply Subtype.ext
  rw [supportedRadicalMixedEquation_fderiv_apply a r w hw Q f hA hC J Y k,
    supportedRadicalNormalResidual_fderiv_apply a r w hw Q f hA hC (J.comp Y) k]
  rfl

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

attribute [local instance] localRadicalCoordinateOperatorNormed localRadicalCoordinateOperatorSpace

/-- The actual two-block chart domain in the ORIGINAL operator space. Both inverses are
native genuine continuous-linear-equivalence blocks. Source: `prop:supported-rank`. -/
def supportedKernelLocalDomain (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ) :
    Set (SymmetricSquare V →L[ℝ] W) :=
  {C | (supportedKernelRightBlock (supportedRankKernelChartOperator B hB C)).IsInvertible ∧
    (supportedKernelRightBlock
      (supportedRadicalRows a r (supportedKernelRadicalFamily B hB U d C))).IsInvertible}

/-- The genuine two-block domain is OPEN. Smoothness is checked at every first-block
point before taking the second block's open preimage; no common smooth neighborhood is
inferred from just a single ContDiffAt-infinity assertion. Source: `prop:supported-rank`. -/
theorem isOpen_supportedKernelLocalDomain (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ) :
    IsOpen (supportedKernelLocalDomain B hB U d a r) := by
  let R : (SymmetricSquare V →L[ℝ] W) →L[ℝ] (B.kerᗮ →L[ℝ] B.kerᗮ) :=
    supportedKernelRightBlock.comp (supportedRankKernelChartOperator B hB)
  let Ω : Set (SymmetricSquare V →L[ℝ] W) := {C | (R C).IsInvertible}
  have hΩ : IsOpen Ω := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage R.continuous
  let A : (B.ker →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) →L[ℝ] (U →L[ℝ] U) :=
    supportedKernelRightBlock.comp (supportedRadicalRows a r)
  let T : (SymmetricSquare V →L[ℝ] W) → (U →L[ℝ] U) :=
    fun C ↦ A (supportedKernelRadicalFamily B hB U d C)
  have hT : ContinuousOn T Ω := by
    intro C hC
    obtain ⟨e, he⟩ := hC
    have hF := (supportedKernelRadicalFamily_contDiffAt B hB U d C e he.symm).continuousAt
    exact (A.continuous.continuousAt.comp hF).continuousWithinAt
  exact hT.isOpen_inter_preimage hΩ ContinuousLinearMap.isOpen_setOfPred_isInvertible

/-- On the WHOLE genuine open two-block domain the SAME actual equation is C-infinity.
Source: `prop:supported-rank`, actual local defining-submersion smoothness. -/
theorem supportedKernelRadicalEquation_contDiffOn (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1) :
    ContDiffOn ℝ ∞ (supportedKernelRadicalEquation B hB U d a r w hw)
      (supportedKernelLocalDomain B hB U d a r) := by
  intro C hC
  obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := hC
  exact (supportedKernelRadicalEquation_contDiffAt B hB U d a r w hw C e he.symm
    f hf.symm).contDiffWithinAt

/-- The SAME actual equation cuts out the literal supported-kernel locus on the WHOLE
chart domain, not only at its center. Source: `prop:supported-rank`, local zero locus. -/
theorem supportedKernelRadicalEquation_domain_zero_iff (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1) (C : SymmetricSquare V →L[ℝ] W)
    (hC : C ∈ supportedKernelLocalDomain B hB U d a r) :
    supportedKernelRadicalEquation B hB U d a r w hw C = 0 ↔
      HasSupportedKernel C.toLinearMap := by
  obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := hC
  exact supportedKernelRadicalEquation_eq_zero_iff B hB U d a r w hw C e he.symm f hf.symm

/-- The sole actual kernel graph is zero at its own center.
Source: `prop:supported-rank`, actual base kernel splitting. -/
theorem supportedKernelGraph_base_eq_zero (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) : supportedRankKernelGraph B hB B = 0 := by
  simp only [supportedRankKernelGraph, supportedKernelBlockGraph,
    supportedRankKernelChartOperator_left, ContinuousLinearMap.comp_zero, neg_zero]

/-- The actual original B-equation is EXACTLY the SAME affine residual applied to the sole
actual kernel graph, as an identity of total functions, not a formal differential premise.
Source: `prop:supported-rank`, the actual local kernel graph equations. -/
theorem supportedKernelRadicalEquation_eq_mixed_graph (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1) (C : SymmetricSquare V →L[ℝ] W) :
    supportedKernelRadicalEquation B hB U d a r w hw C =
      supportedRadicalMixedEquation a r w hw
        ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)
        ((supportedRadicalCoordinateOperatorMap U d).comp B.kerᗮ.subtypeL)
        (supportedRankKernelGraph B hB C) := by
  apply congrArg (supportedRadicalNormalResidual a r w hw)
  apply ContinuousLinearMap.ext
  intro k
  apply ContinuousLinearMap.ext
  intro v
  change supportedRadicalCoordinateOperatorMap U d
      ((k : SymmetricSquare V) + (supportedRankKernelGraph B hB C k : SymmetricSquare V)) v =
    (supportedRadicalCoordinateOperatorMap U d (k : SymmetricSquare V)) v +
      (supportedRadicalCoordinateOperatorMap U d
        (supportedRankKernelGraph B hB C k : SymmetricSquare V)) v
  rw [map_add]
  rfl

/-- The true original B-equation derivative is the SAME mixed residual derivative composed
with the ACTUAL kernel-map derivative. Source: `prop:supported-rank`, equation (9.4).
All differentiability and the exact global function identity are proved internally. -/
theorem supportedKernelRadicalEquation_hasFDerivAt (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1) (f : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r
      ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)) =
        (f : U →L[ℝ] U)) :
    HasFDerivAt (supportedKernelRadicalEquation B hB U d a r w hw)
      ((fderiv ℝ (supportedRadicalMixedEquation a r w hw
        ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)
        ((supportedRadicalCoordinateOperatorMap U d).comp B.kerᗮ.subtypeL)) 0).comp
          (fderiv ℝ (supportedRankKernelGraph B hB) B)) B := by
  let Q := (supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL
  let J := (supportedRadicalCoordinateOperatorMap U d).comp B.kerᗮ.subtypeL
  let N := supportedRadicalMixedEquation a r w hw Q J
  let A : (B.ker →L[ℝ] B.kerᗮ) →L[ℝ]
      (B.ker →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) :=
    ContinuousLinearMap.compL ℝ B.ker B.kerᗮ ((ℝ × U) →L[ℝ] (ℝ × U)) J
  have hA0 : Q + A (0 : B.ker →L[ℝ] B.kerᗮ) = Q := by
    apply ContinuousLinearMap.ext
    intro k
    apply ContinuousLinearMap.ext
    intro v
    change Q k v + J (0 : B.kerᗮ) v = Q k v
    rw [J.map_zero]
    exact add_zero _
  have hlinear : ContDiff ℝ ∞ A := by fun_prop
  have hparam : ContDiffAt ℝ ∞ (fun Y : B.ker →L[ℝ] B.kerᗮ ↦ Q + A Y) 0 :=
    contDiffAt_const.add hlinear.contDiffAt
  have hnormal : ContDiffAt ℝ ∞ (supportedRadicalNormalResidual a r w hw)
      (Q + A (0 : B.ker →L[ℝ] B.kerᗮ)) := by
    rw [hA0]
    exact supportedRadicalNormalResidual_contDiffAt a r w hw Q f hA
  have hN : ContDiffAt ℝ ∞ N 0 := by
    simpa only [N, supportedRadicalMixedEquation, A] using! hnormal.comp 0 hparam
  have hNg : HasFDerivAt N (fderiv ℝ N 0) (supportedRankKernelGraph B hB B) := by
    rw [supportedKernelGraph_base_eq_zero]
    exact (hN.differentiableAt (by simp)).hasFDerivAt
  have hG : HasFDerivAt (supportedRankKernelGraph B hB)
      (fderiv ℝ (supportedRankKernelGraph B hB) B) B :=
    ((supportedRankKernelGraph_contDiffAt B hB).differentiableAt (by simp)).hasFDerivAt
  have hd := HasFDerivAt.comp (𝕜 := ℝ) (E := SymmetricSquare V →L[ℝ] W)
    (F := B.ker →L[ℝ] B.kerᗮ) (G := B.ker →L[ℝ] r.ker) B hNg hG
  have hid : (N ∘ supportedRankKernelGraph B hB) =
      supportedKernelRadicalEquation B hB U d a r w hw := by
    funext C
    exact (supportedKernelRadicalEquation_eq_mixed_graph B hB U d a r w hw C).symm
  rw [hid] at hd
  exact hd

/-- The derivative of the ORIGINAL B-equation is genuinely onto, realized by actual
symmetric tensors followed by the actual onto kernel-map derivative. Source:
`prop:supported-rank`, original local defining-submersion construction. -/
theorem supportedKernelRadicalEquation_fderiv_surjective
    (B : SymmetricSquare V →L[ℝ] W) (hB : Function.Surjective B)
    (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (e : V) (he : ‖e‖ = 1) (hde : d (1, 0) = e)
    (hK : ∀ q ∈ B.ker, (symmetricSquareToSelfAdjoint q).val e = 0)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1) (f : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r
      ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)) =
        (f : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r
      ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)) = 0) :
    Function.Surjective (fderiv ℝ (supportedKernelRadicalEquation B hB U d a r w hw) B) := by
  rw [(supportedKernelRadicalEquation_hasFDerivAt B hB U d a r w hw f hA).fderiv]
  exact (supportedKernelRadicalMixed_fderiv_surjective B.ker U d e he hde hK a r w hw
    ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL) f hA hC).comp
      (supportedKernelGraph_fderiv_surjective B hB)

/-- The SAME original equation derivative factors through the GENUINE actual mixed
projection of the actual kernel derivative. Evaluation preservation is proved internally
from the original Hilbert pairing. Source: `prop:supported-rank`, actual normal quotient. -/
theorem supportedKernelRadicalEquation_fderiv_projection_factor
    (B : SymmetricSquare V →L[ℝ] W) (hB : Function.Surjective B)
    (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V) (e : V) (hde : d (1, 0) = e)
    (hZ : LinearMap.range (symmetricSquareProduct V e) ≤ B.kerᗮ)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1) (f : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r
      ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)) =
        (f : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r
      ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)) = 0)
    (Δ : SymmetricSquare V →L[ℝ] W) :
    fderiv ℝ (supportedKernelRadicalEquation B hB U d a r w hw) B Δ =
      fderiv ℝ (supportedRadicalMixedEquation a r w hw
        ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)
        ((supportedRadicalCoordinateOperatorMap U d).comp (B.kerᗮ.subtypeL.comp
          ((LinearMap.range (symmetricSquareProduct V e)).comap B.kerᗮ.subtype).subtypeL))) 0
        ((Submodule.orthogonalProjectionOnto
          ((LinearMap.range (symmetricSquareProduct V e)).comap B.kerᗮ.subtype)).comp
            (fderiv ℝ (supportedRankKernelGraph B hB) B Δ)) := by
  rw [(supportedKernelRadicalEquation_hasFDerivAt B hB U d a r w hw f hA).fderiv,
    ContinuousLinearMap.comp_apply]
  rw [supportedKernelRadicalMixed_fderiv_eq_normal B.ker U a r w hw _ f hA hC,
    supportedKernelRadicalMixed_fderiv_eq_normal B.ker U a r w hw _ f hA hC]
  apply supportedRadicalNormalResidual_fderiv_projection_factor a r w hw _ f hA hC
    ((supportedRadicalCoordinateOperatorMap U d).comp B.kerᗮ.subtypeL)
    ((LinearMap.range (symmetricSquareProduct V e)).comap B.kerᗮ.subtype).subtypeL
    ((LinearMap.range (symmetricSquareProduct V e)).comap B.kerᗮ.subtype).orthogonalProjectionOnto
  intro q
  exact supportedKernel_mixed_projection_coordinate_evaluation B.kerᗮ U d e hde hZ q

/-- The actual transported kernel family at the base is the literal kernel inclusion.
Source: `prop:supported-rank`, fixed actual kernel coordinates. -/
theorem supportedKernelRadicalFamily_base (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V) :
    supportedKernelRadicalFamily B hB U d B =
      (supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL := by
  apply ContinuousLinearMap.ext
  intro k
  apply ContinuousLinearMap.ext
  intro v
  change supportedRadicalCoordinateOperatorMap U d
      ((k : SymmetricSquare V) + (supportedRankKernelGraph B hB B k : SymmetricSquare V)) v =
    supportedRadicalCoordinateOperatorMap U d (k : SymmetricSquare V) v
  rw [supportedKernelGraph_base_eq_zero]
  simp only [zero_apply, Submodule.coe_zero, add_zero]

/-- Actual unit-normal and good-block data produce a TRUE chart and its SAME finite
normal differential factorization. All local geometry, submersion and kernel estimates
are constructed, not assumed. The final original-data wrapper supplies these algebraic
choices internally. Source: `prop:supported-rank`, original strong-rank geometry. -/
theorem exists_supportedKernelLocalEquations_actual
    [FiniteDimensional ℝ W]
    (B : SymmetricSquare V →L[ℝ] W) (hB : Function.Surjective B)
    (hphase : LinearSecondFormPhaseRegular B.toLinearMap)
    (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (e : V) (he : ‖e‖ = 1) (hde : d (1, 0) = e)
    (hK : ∀ q ∈ B.ker, (symmetricSquareToSelfAdjoint q).val e = 0)
    (hZ : LinearMap.range (symmetricSquareProduct V e) ≤ B.kerᗮ)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1) (f : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r
      ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)) =
        (f : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r
      ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)) = 0) :
    ∃ chart : SupportedLocusLocalEquations
        {C : SymmetricSquare V →L[ℝ] W |
          Function.Surjective C ∧ LinearSecondFormPhaseRegular C.toLinearMap}
        {C : SymmetricSquare V →L[ℝ] W | HasSupportedKernel C.toLinearMap} B,
      ∃ M : (B.ker →ₗ[ℝ] supportedRankActualMixedSpace B e) →ₗ[ℝ]
          (Fin chart.codim → ℝ),
        (∀ Δ, fderiv ℝ chart.equation B Δ =
          M (supportedRankProjectedKernelVariation B hB e Δ).toLinearMap) ∧
            Module.finrank ℝ M.ker ≤ Module.finrank ℝ U := by
  let F := supportedKernelRadicalEquation B hB U d a r w hw
  let X := B.ker →L[ℝ] r.ker
  have : FiniteDimensional ℝ X := inferInstance
  have : Module.Free ℝ X := Module.Free.of_divisionRing ℝ X
  let b : X ≃ₗ[ℝ] (Fin (Module.finrank ℝ X) → ℝ) := (Module.finBasis ℝ X).equivFun
  let τ : X ≃L[ℝ] (Fin (Module.finrank ℝ X) → ℝ) :=
    { toLinearEquiv := b
      continuous_toFun := LinearMap.continuous_of_finiteDimensional
        (𝕜 := ℝ) (E := X) (F' := Fin (Module.finrank ℝ X) → ℝ) b.toLinearMap
      continuous_invFun := LinearMap.continuous_of_finiteDimensional
        (𝕜 := ℝ) (E := Fin (Module.finrank ℝ X) → ℝ) (F' := X) b.symm.toLinearMap }
  let E : (SymmetricSquare V →L[ℝ] W) → (Fin (Module.finrank ℝ X) → ℝ) := fun C ↦ τ (F C)
  let ambient : Set (SymmetricSquare V →L[ℝ] W) :=
    {C | Function.Surjective C ∧ LinearSecondFormPhaseRegular C.toLinearMap}
  let D := supportedKernelLocalDomain B hB U d a r ∩ ambient
  have hDopen : IsOpen D :=
    (isOpen_supportedKernelLocalDomain B hB U d a r).inter
      isOpen_surjective_linearSecondFormPhaseRegular
  have hDb : B ∈ D := by
    refine ⟨⟨⟨ContinuousLinearEquiv.refl ℝ B.kerᗮ, ?_⟩, ⟨f, ?_⟩⟩, hB, hphase⟩
    · exact (supportedRankKernelChartOperator_right B hB).symm
    · rw [supportedKernelRadicalFamily_base]
      exact hA.symm
  have hF : ContDiffOn ℝ ∞ F D :=
    (supportedKernelRadicalEquation_contDiffOn B hB U d a r w hw).mono Set.inter_subset_left
  have hE : ContDiffOn ℝ ∞ E D := by
    simpa only [E, Function.comp_def] using! τ.contDiff.comp_contDiffOn hF
  have hFder : HasFDerivAt F (fderiv ℝ F B) B :=
    (supportedKernelRadicalEquation_hasFDerivAt B hB U d a r w hw f
      hA).differentiableAt.hasFDerivAt
  have hτ : HasFDerivAt (fun v : X ↦ τ v)
      (τ : X →L[ℝ] (Fin (Module.finrank ℝ X) → ℝ)) (F B) := by
    simpa using! (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := X)
      (F := Fin (Module.finrank ℝ X) → ℝ) τ.toContinuousLinearMap (x := F B))
  have hEder : HasFDerivAt E
      ((τ : X →L[ℝ] (Fin (Module.finrank ℝ X) → ℝ)).comp (fderiv ℝ F B)) B := by
    simpa only [E] using! (HasFDerivAt.comp (𝕜 := ℝ)
      (E := SymmetricSquare V →L[ℝ] W) (F := X)
      (G := Fin (Module.finrank ℝ X) → ℝ) B hτ hFder)
  have hEsurj : Function.Surjective (fderiv ℝ E B) := by
    rw [hEder.fderiv]
    exact τ.surjective.comp
      (supportedKernelRadicalEquation_fderiv_surjective B hB U d e he hde hK
        a r w hw f hA hC)
  let chart : SupportedLocusLocalEquations ambient
      {C : SymmetricSquare V →L[ℝ] W | HasSupportedKernel C.toLinearMap} B :=
    { codim := Module.finrank ℝ X
      domain := D
      equation := E
      isOpen_domain := hDopen
      mem_domain := hDb
      domain_subset := Set.inter_subset_right
      contDiffOn_equation := hE
      mem_locus_iff := by
        intro C hCD
        change HasSupportedKernel C.toLinearMap ↔ τ (F C) = 0
        rw [τ.map_eq_zero_iff]
        exact (supportedKernelRadicalEquation_domain_zero_iff B hB U d a r w hw C hCD.1).symm
      surjective_fderiv := hEsurj }
  let Z := supportedRankActualMixedSpace B e
  let J := (supportedRadicalCoordinateOperatorMap U d).comp (B.kerᗮ.subtypeL.comp Z.subtypeL)
  let Q := (supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL
  let N := fderiv ℝ (supportedRadicalMixedEquation a r w hw Q J) 0
  let c : (B.ker →ₗ[ℝ] Z) ≃ₗ[ℝ] (B.ker →L[ℝ] Z) := LinearMap.toContinuousLinearMap
  let M : (B.ker →ₗ[ℝ] Z) →ₗ[ℝ] (Fin chart.codim → ℝ) :=
    (τ.toLinearMap.comp N.toLinearMap).comp c.toLinearMap
  refine ⟨chart, M, ?_, ?_⟩
  · intro Δ
    change fderiv ℝ E B Δ = τ (N (c
      (supportedRankProjectedKernelVariation B hB e Δ).toLinearMap))
    rw [hEder.fderiv, ContinuousLinearMap.comp_apply]
    apply congrArg τ
    change fderiv ℝ F B Δ = N (Z.orthogonalProjectionOnto.comp
      (fderiv ℝ (supportedRankKernelGraph B hB) B Δ))
    exact supportedKernelRadicalEquation_fderiv_projection_factor B hB U d e hde hZ
      a r w hw f hA hC Δ
  · let g : M.ker →ₗ[ℝ] N.ker :=
      (c.toLinearMap.comp M.ker.subtype).codRestrict N.ker (by
        intro v
        change N (c v.val) = 0
        apply τ.injective
        change M v.val = τ 0
        rw [v.property, map_zero])
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      apply c.injective
      exact congrArg (fun v : N.ker ↦ (v : B.ker →L[ℝ] Z)) hxy
    have heinner : inner ℝ e e = 1 := by
      rw [real_inner_self_eq_norm_sq, he]
      norm_num
    exact (LinearMap.finrank_le_finrank_of_injective hg).trans
      (supportedKernelRadicalMixed_kernel_finrank_le B.ker U d e heinner hde
        a r w hw Q f hA hC)

/-- FULL original supported-locus geometry and SAME-chart normal-factor contract.
Every local choice is constructed from the original onto/phase/dimension/support data:
choose a unit normal in the GIVEN original hyperplane's orthogonal complement, reuse
native hyperplane coordinates, original Riesz/good E/J and the genuine scalar row blocks,
then construct the actual finite chart and its derivative map. The normal kernel loses
at most the original n-1 dimensions. No local chart, factorization, submersion or rank
bound is an input. Source: `prop:supported-rank`, lines 998–1029; exact W6 final contract. -/
theorem exists_supportedKernelLocalEquations_original
    [FiniteDimensional ℝ W]
    (B : SymmetricSquare V →L[ℝ] W) (hB : Function.Surjective B)
    (hphase : LinearSecondFormPhaseRegular B.toLinearMap)
    (hn : 3 ≤ Module.finrank ℝ V)
    (hW : Module.finrank ℝ W =
      Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 + 1)
    (U : Submodule ℝ V) (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V)
    (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range) :
    ∃ e : V, e ∈ Uᗮ ∧ e ≠ 0 ∧
      ∃ chart : SupportedLocusLocalEquations
          {C : SymmetricSquare V →L[ℝ] W |
            Function.Surjective C ∧ LinearSecondFormPhaseRegular C.toLinearMap}
          {C : SymmetricSquare V →L[ℝ] W | HasSupportedKernel C.toLinearMap} B,
        ∃ M : (B.ker →ₗ[ℝ] supportedRankActualMixedSpace B e) →ₗ[ℝ]
            (Fin chart.codim → ℝ),
          (∀ Δ, fderiv ℝ chart.equation B Δ =
            M (supportedRankProjectedKernelVariation B hB e Δ).toLinearMap) ∧
              Module.finrank ℝ M.ker ≤ Module.finrank ℝ V - 1 := by
  have hp : 0 < Module.finrank ℝ Uᗮ := by
    have hd := U.finrank_add_finrank_orthogonal
    omega
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := Uᗮ)).mp hp
  let e₀ : Uᗮ := ‖v‖⁻¹ • v
  have heunit : ‖e₀‖ = 1 := by simp [e₀, norm_smul, hv]
  let e : V := e₀
  have he : ‖e‖ = 1 := heunit
  have he0 : e ≠ 0 := by
    intro hz
    simp [hz] at he
  have heU : e ∈ Uᗮ := e₀.property
  let d : (ℝ × U) ≃L[ℝ] V :=
    (ContinuousLinearEquiv.prodComm ℝ ℝ U).trans
      (supportedRankHyperplaneCoordinates U hU e heU he0).toContinuousLinearEquiv
  have hdU (u : U) : d (0, u) = (u : V) := by
    change (u : V) + (0 : ℝ) • e = (u : V)
    simp
  have hde : d (1, 0) = e := by
    change (0 : V) + (1 : ℝ) • e = e
    simp
  have hkill : ∀ q ∈ B.ker, (symmetricSquareToSelfAdjoint q).val e = 0 := by
    intro q hq
    have h := supportedRank_kernel_operator_lift B.toLinearMap U hK ⟨q, hq⟩
      (0 : U) e heU (1 : ℝ)
    simpa only [Submodule.coe_zero, zero_add, one_smul, map_zero] using h
  have hZ := symmetricSquare_mixed_range_le_orthogonal U B.ker hK e heU
  have hdK := symmetricSquare_surjective_kernel_finrank B.toLinearMap hB hW
  have hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U := by omega
  have hpos : 0 < Module.finrank ℝ U := by omega
  obtain ⟨ξ, hgξ⟩ := hphase
  obtain ⟨x, _, hg⟩ := supportedRank_good_covector_riesz B.toLinearMap ξ hgξ
  have hz := supportedRank_good_projection_ne_zero B.toLinearMap U hK x hg hdim hpos
  let a := supportedRadicalGoodRowEquiv B.toLinearMap U hK x hg hdim
  let r := supportedRadicalScalarTest U x d
  obtain ⟨w, hw⟩ := supportedRadicalScalarTest_exists_section U x d hz
  have hA := supportedRadicalGoodRow_rightBlock B.toLinearMap U hK x hg hdim d hdU
  have hC := supportedRadicalGoodRow_leftBlock B.toLinearMap U hK x hg hdim d e heU hde
  obtain ⟨chart, M, hf, hk⟩ := exists_supportedKernelLocalEquations_actual B hB
    ⟨ξ, hgξ⟩ U d e he hde hkill hZ a r w hw (ContinuousLinearEquiv.refl ℝ U) hA hC
  refine ⟨e, heU, he0, chart, M, hf, ?_⟩
  have hdU' : Module.finrank ℝ U = Module.finrank ℝ V - 1 := by omega
  exact hk.trans (by omega)

end GlobalEmbedding.Paper
