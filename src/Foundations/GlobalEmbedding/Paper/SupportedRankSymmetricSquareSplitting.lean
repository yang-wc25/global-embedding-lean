import GlobalEmbedding.Paper.SymmetricSquare
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:supported-rank`, lines 1007–1008. This module makes the splitting assumption explicit as
an actual linear equivalence `U × ℝ ≃ V` and constructs the quotient decomposition. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {U V : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- The `U` coordinate from a chosen direct-sum equivalence. -/
def supportedRankSplitProjection (d : (U × ℝ) ≃ₗ[ℝ] V) : V →ₗ[ℝ] U :=
  (LinearMap.fst ℝ U ℝ).comp d.symm.toLinearMap

/-- The scalar coordinate from a chosen direct-sum equivalence. -/
def supportedRankSplitScalar (d : (U × ℝ) ≃ₗ[ℝ] V) : V →ₗ[ℝ] ℝ :=
  (LinearMap.snd ℝ U ℝ).comp d.symm.toLinearMap

/-- The inclusion of the `U` summand. -/
def supportedRankSplitInclusion (d : (U × ℝ) ≃ₗ[ℝ] V) : U →ₗ[ℝ] V :=
  d.toLinearMap.comp (LinearMap.inl ℝ U ℝ)

/-- The distinguished vector corresponding to the scalar summand. -/
def supportedRankSplitVector (d : (U × ℝ) ≃ₗ[ℝ] V) : V := d (0, 1)

/-- Coordinates of a tensor in the two summands of the symmetric-square quotient, before
factoring through the quotient. -/
noncomputable def supportedRankSplitTensorMap (d : (U × ℝ) ≃ₗ[ℝ] V) :
    (V ⊗[ℝ] V) →ₗ[ℝ] SymmetricSquare U × V := by
  let p := supportedRankSplitProjection d
  let a := supportedRankSplitScalar d
  let e := supportedRankSplitVector d
  let j := supportedRankSplitInclusion d
  let f₁ := (symmetricSquareQuotient U).comp (TensorProduct.map p p)
  let f₂ := j.comp ((TensorProduct.lid ℝ U).toLinearMap.comp (TensorProduct.map a p)) +
    j.comp ((TensorProduct.rid ℝ U).toLinearMap.comp (TensorProduct.map p a)) +
    (LinearMap.toSpanSingleton ℝ V e).comp
      ((TensorProduct.lid ℝ ℝ).toLinearMap.comp (TensorProduct.map a a))
  exact LinearMap.prod f₁ f₂

/-- The first coordinate evaluates on pure tensors by projection to `U`. -/
@[simp] theorem supportedRankSplitTensorMap_fst_tmul (d : (U × ℝ) ≃ₗ[ℝ] V)
    (v w : V) :
    (supportedRankSplitTensorMap d (v ⊗ₜ[ℝ] w)).1 =
      symmetricSquareProduct U (supportedRankSplitProjection d v)
        (supportedRankSplitProjection d w) := by
  simp [supportedRankSplitTensorMap, LinearMap.prod_apply, symmetricSquareProduct_apply]

private theorem supportedRankSplit_d_inl_smul (d : (U × ℝ) ≃ₗ[ℝ] V)
    (c : ℝ) (u : U) : d (c • u, (0 : ℝ)) = c • d (u, 0) := by
  have h : (c • u, (0 : ℝ)) = c • (u, 0) := by ext <;> simp
  rw [h, map_smul]

/-- The second coordinate evaluates on pure tensors by the mixed and scalar components. -/
@[simp] theorem supportedRankSplitTensorMap_snd_tmul (d : (U × ℝ) ≃ₗ[ℝ] V)
    (v w : V) :
    (supportedRankSplitTensorMap d (v ⊗ₜ[ℝ] w)).2 =
      (supportedRankSplitScalar d v) •
          supportedRankSplitInclusion d (supportedRankSplitProjection d w) +
        (supportedRankSplitScalar d w) •
          supportedRankSplitInclusion d (supportedRankSplitProjection d v) +
        (supportedRankSplitScalar d v * supportedRankSplitScalar d w) •
          supportedRankSplitVector d := by
  simp [supportedRankSplitTensorMap, LinearMap.prod_apply, Function.prod_apply,
    LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul,
    TensorProduct.rid_tmul, LinearMap.toSpanSingleton_apply,
    supportedRankSplitProjection, supportedRankSplitScalar, supportedRankSplitVector,
    supportedRankSplitInclusion, LinearMap.inl_apply,
    supportedRankSplit_d_inl_smul]

/-- The coordinate tensor map kills every antisymmetric generator. -/
theorem supportedRankSplitTensorMap_killsRelations (d : (U × ℝ) ≃ₗ[ℝ] V) :
    symmetricSquareRelations V ≤ LinearMap.ker (supportedRankSplitTensorMap d) := by
  rw [symmetricSquareRelations]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨v, w⟩, rfl⟩
  change supportedRankSplitTensorMap d (v ⊗ₜ[ℝ] w - w ⊗ₜ[ℝ] v) = 0
  rw [map_sub]
  ext
  · change (supportedRankSplitTensorMap d (v ⊗ₜ[ℝ] w)).1 -
        (supportedRankSplitTensorMap d (w ⊗ₜ[ℝ] v)).1 = 0
    rw [supportedRankSplitTensorMap_fst_tmul, supportedRankSplitTensorMap_fst_tmul]
    exact sub_eq_zero.mpr (symmetricSquareProduct_comm U _ _)
  · simp [add_comm, add_assoc, mul_comm]

/-- The coordinates descend to the exact binary symmetric-square quotient. -/
noncomputable def supportedRankSplitQuotientMap (d : (U × ℝ) ≃ₗ[ℝ] V) :
    SymmetricSquare V →ₗ[ℝ] SymmetricSquare U × V :=
  (symmetricSquareRelations V).liftQ (supportedRankSplitTensorMap d)
    (supportedRankSplitTensorMap_killsRelations d)

@[simp] theorem supportedRankSplitQuotientMap_mk (d : (U × ℝ) ≃ₗ[ℝ] V)
    (z : V ⊗[ℝ] V) :
    supportedRankSplitQuotientMap d (Submodule.Quotient.mk z) =
      supportedRankSplitTensorMap d z := rfl

@[simp] theorem supportedRankSplitProjection_inclusion (d : (U × ℝ) ≃ₗ[ℝ] V)
    (u : U) : supportedRankSplitProjection d (supportedRankSplitInclusion d u) = u := by
  simp [supportedRankSplitProjection, supportedRankSplitInclusion]

@[simp] theorem supportedRankSplitScalar_inclusion (d : (U × ℝ) ≃ₗ[ℝ] V)
    (u : U) : supportedRankSplitScalar d (supportedRankSplitInclusion d u) = 0 := by
  simp [supportedRankSplitScalar, supportedRankSplitInclusion]

@[simp] theorem supportedRankSplitProjection_vector (d : (U × ℝ) ≃ₗ[ℝ] V) :
    supportedRankSplitProjection d (supportedRankSplitVector d) = 0 := by
  simp [supportedRankSplitProjection, supportedRankSplitVector]

@[simp] theorem supportedRankSplitScalar_vector (d : (U × ℝ) ≃ₗ[ℝ] V) :
    supportedRankSplitScalar d (supportedRankSplitVector d) = 1 := by
  simp [supportedRankSplitScalar, supportedRankSplitVector]

/-- Every vector is the sum of its `U` coordinate and scalar multiple of the complement. -/
theorem supportedRankSplit_decompose (d : (U × ℝ) ≃ₗ[ℝ] V) (v : V) :
    supportedRankSplitInclusion d (supportedRankSplitProjection d v) +
        supportedRankSplitScalar d v • supportedRankSplitVector d = v := by
  apply d.symm.injective
  simp [supportedRankSplitInclusion, supportedRankSplitProjection, supportedRankSplitScalar,
    supportedRankSplitVector]

/-- The tensor-square of the `U` inclusion preserves the relation submodule. -/
theorem supportedRankSplitInclusion_preservesRelations (d : (U × ℝ) ≃ₗ[ℝ] V) :
    symmetricSquareRelations U ≤ (symmetricSquareRelations V).comap
      (TensorProduct.map (supportedRankSplitInclusion d) (supportedRankSplitInclusion d)) := by
  rw [symmetricSquareRelations, symmetricSquareRelations]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨u, w⟩, rfl⟩
  change TensorProduct.map (supportedRankSplitInclusion d) (supportedRankSplitInclusion d)
    (u ⊗ₜ[ℝ] w - w ⊗ₜ[ℝ] u) ∈ symmetricSquareRelations V
  rw [map_sub, TensorProduct.map_tmul, TensorProduct.map_tmul]
  exact Submodule.subset_span ⟨(supportedRankSplitInclusion d u,
    supportedRankSplitInclusion d w), rfl⟩

/-- The induced inclusion of the `U` symmetric square into the ambient quotient. -/
noncomputable def supportedRankSplitSymmetricSquareInclusion
    (d : (U × ℝ) ≃ₗ[ℝ] V) : SymmetricSquare U →ₗ[ℝ] SymmetricSquare V :=
  (symmetricSquareRelations U).mapQ (symmetricSquareRelations V)
    (TensorProduct.map (supportedRankSplitInclusion d) (supportedRankSplitInclusion d))
    (supportedRankSplitInclusion_preservesRelations d)

@[simp] theorem supportedRankSplitSymmetricSquareInclusion_mk
    (d : (U × ℝ) ≃ₗ[ℝ] V) (z : U ⊗[ℝ] U) :
    supportedRankSplitSymmetricSquareInclusion d (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (TensorProduct.map (supportedRankSplitInclusion d) (supportedRankSplitInclusion d) z) := rfl

/-- Coordinates of the included `Sym²U` summand. -/
theorem supportedRankSplitQuotientMap_inclusion (d : (U × ℝ) ≃ₗ[ℝ] V)
    (q : SymmetricSquare U) :
    supportedRankSplitQuotientMap d (supportedRankSplitSymmetricSquareInclusion d q) = (q, 0) := by
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
    rw [supportedRankSplitSymmetricSquareInclusion_mk, supportedRankSplitQuotientMap_mk]
    induction z using TensorProduct.inductionOn with
    | tmul u w =>
        rw [TensorProduct.map_tmul]
        apply Prod.ext
        · rw [supportedRankSplitTensorMap_fst_tmul]
          simp [symmetricSquareProduct_apply, symmetricSquareQuotient]
        · rw [supportedRankSplitTensorMap_snd_tmul]
          simp
    | add z₁ z₂ hz₁ hz₂ =>
        simp only [map_add, hz₁, hz₂]
        ext <;> simp

/-- Coordinates of the map `v ↦ e ⊙ v`; its image supplies the complementary summand. -/
theorem supportedRankSplitQuotientMap_product (d : (U × ℝ) ≃ₗ[ℝ] V)
    (v : V) :
    supportedRankSplitQuotientMap d (symmetricSquareProduct V (supportedRankSplitVector d) v) =
      (0, v) := by
  rw [symmetricSquareProduct_apply]
  change supportedRankSplitQuotientMap d
    (Submodule.Quotient.mk (supportedRankSplitVector d ⊗ₜ[ℝ] v)) = (0, v)
  rw [supportedRankSplitQuotientMap_mk]
  apply Prod.ext
  · rw [supportedRankSplitTensorMap_fst_tmul]
    simp
  · rw [supportedRankSplitTensorMap_snd_tmul]
    simp [supportedRankSplit_decompose]

/-- Reconstruct a quotient class from its `Sym²U` coordinate and its `e ⊙ V` coordinate. -/
noncomputable def supportedRankSplitReconstruct (d : (U × ℝ) ≃ₗ[ℝ] V) :
    SymmetricSquare U × V →ₗ[ℝ] SymmetricSquare V :=
  (supportedRankSplitSymmetricSquareInclusion d).comp
      (LinearMap.fst ℝ (SymmetricSquare U) V) +
    (symmetricSquareProduct V (supportedRankSplitVector d)).comp
      (LinearMap.snd ℝ (SymmetricSquare U) V)

/-- Inclusion of the `U` quotient commutes with the canonical symmetric product. -/
theorem supportedRankSplitSymmetricSquareInclusion_product
    (d : (U × ℝ) ≃ₗ[ℝ] V) (u w : U) :
    supportedRankSplitSymmetricSquareInclusion d (symmetricSquareProduct U u w) =
      symmetricSquareProduct V (supportedRankSplitInclusion d u)
        (supportedRankSplitInclusion d w) := by
  rw [symmetricSquareProduct_apply]
  change supportedRankSplitSymmetricSquareInclusion d
    (Submodule.Quotient.mk (u ⊗ₜ[ℝ] w)) = _
  rw [supportedRankSplitSymmetricSquareInclusion_mk, TensorProduct.map_tmul,
    symmetricSquareProduct_apply]
  rfl

/-- The symmetric product expands in the chosen direct-sum coordinates. -/
theorem supportedRankSplit_product_decompose (d : (U × ℝ) ≃ₗ[ℝ] V) (v w : V) :
    symmetricSquareProduct V v w =
      symmetricSquareProduct V (supportedRankSplitInclusion d (supportedRankSplitProjection d v))
          (supportedRankSplitInclusion d (supportedRankSplitProjection d w)) +
        symmetricSquareProduct V (supportedRankSplitVector d)
          (supportedRankSplitScalar d v •
              supportedRankSplitInclusion d (supportedRankSplitProjection d w) +
            supportedRankSplitScalar d w •
              supportedRankSplitInclusion d (supportedRankSplitProjection d v) +
            (supportedRankSplitScalar d v * supportedRankSplitScalar d w) •
              supportedRankSplitVector d) := by
  conv_lhs =>
    rw [← supportedRankSplit_decompose d v, ← supportedRankSplit_decompose d w]
  let β := symmetricSquareProduct V
  let u := supportedRankSplitInclusion d (supportedRankSplitProjection d v)
  let x := supportedRankSplitInclusion d (supportedRankSplitProjection d w)
  let e := supportedRankSplitVector d
  let a := supportedRankSplitScalar d v
  let b := supportedRankSplitScalar d w
  change β (u + a • e) (x + b • e) = β u x + β e (a • x + b • u + (a * b) • e)
  calc
    β (u + a • e) (x + b • e) =
        β u x + b • β u e + a • β e x + (a * b) • β e e := by
          simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
            smul_add, smul_smul, mul_comm b a]
          abel
    _ = β u x + β e (a • x + b • u + (a * b) • e) := by
          have hcomm : β u e = β e u := symmetricSquareProduct_comm V u e
          rw [hcomm]
          simp only [map_add, map_smul]
          abel

/-- Reconstruction sends the coordinates of a pure tensor back to its quotient class. -/
theorem supportedRankSplitReconstruct_tensor (d : (U × ℝ) ≃ₗ[ℝ] V) (v w : V) :
    supportedRankSplitReconstruct d (supportedRankSplitTensorMap d (v ⊗ₜ[ℝ] w)) =
      symmetricSquareProduct V v w := by
  change supportedRankSplitReconstruct d
    ((supportedRankSplitTensorMap d (v ⊗ₜ[ℝ] w)).1,
      (supportedRankSplitTensorMap d (v ⊗ₜ[ℝ] w)).2) = _
  rw [supportedRankSplitTensorMap_fst_tmul, supportedRankSplitTensorMap_snd_tmul]
  simp only [supportedRankSplitReconstruct, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply,
    supportedRankSplitSymmetricSquareInclusion_product]
  rw [← supportedRankSplit_product_decompose (U := U) (V := V) d v w]

/-- Reconstruction after quotient coordinates is the identity on the exact quotient. -/
theorem supportedRankSplitReconstruct_quotientMap (d : (U × ℝ) ≃ₗ[ℝ] V)
    (q : SymmetricSquare V) :
    supportedRankSplitReconstruct d (supportedRankSplitQuotientMap d q) = q := by
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
    rw [supportedRankSplitQuotientMap_mk]
    induction z using TensorProduct.inductionOn with
    | tmul v w =>
        rw [supportedRankSplitReconstruct_tensor, symmetricSquareProduct_apply]
        rfl
    | add z₁ z₂ hz₁ hz₂ =>
        simp only [map_add, hz₁, hz₂]
        rfl

/-- The coordinate map followed by reconstruction is the identity. -/
theorem supportedRankSplitQuotientMap_reconstruct (d : (U × ℝ) ≃ₗ[ℝ] V)
    (q : SymmetricSquare U) (v : V) :
    supportedRankSplitQuotientMap d (supportedRankSplitReconstruct d (q, v)) = (q, v) := by
  change supportedRankSplitQuotientMap d
    (supportedRankSplitSymmetricSquareInclusion d q +
      symmetricSquareProduct V (supportedRankSplitVector d) v) = (q, v)
  rw [map_add, supportedRankSplitQuotientMap_inclusion, supportedRankSplitQuotientMap_product]
  ext <;> simp


/-- The full supported-rank symmetric-square splitting, on the existing exact quotient.
The two actual summand ranges are complementary, the image of e⊙V has dimension
finrank V, and the linear equivalence reconstructs by the actual sum of inclusions.

Proof: the two proved coordinate identities make the actual quotient coordinate map
and reconstruction mutual inverses. Their restrictions to the two summands are
(q,0) and (0,v), proving both inclusions injective and their ranges disjoint. Every
quotient class is reconstructed from its two coordinates, proving the ranges span.
The image of e⊙· has the dimension of V by injectivity. Finally replace the V factor
of the coordinate equivalence with its actual image via the induced range equivalence.
Source: `prop:supported-rank`, lines 1007–1008. The source n is finrank V; no use of
truncated natural subtraction n−1 is made. No normalized symmetric-tensor model is used. -/
theorem supported_rank_symmetric_square_splitting (d : (U × ℝ) ≃ₗ[ℝ] V) :
    Function.Injective (supportedRankSplitSymmetricSquareInclusion d) ∧
    Function.Injective (symmetricSquareProduct V (supportedRankSplitVector d)) ∧
    IsCompl (LinearMap.range (supportedRankSplitSymmetricSquareInclusion d))
      (LinearMap.range (symmetricSquareProduct V (supportedRankSplitVector d))) ∧
    Module.finrank ℝ
      (LinearMap.range (symmetricSquareProduct V (supportedRankSplitVector d))) =
        Module.finrank ℝ V ∧
    ∃ Φ : SymmetricSquare V ≃ₗ[ℝ]
        SymmetricSquare U ×
          LinearMap.range (symmetricSquareProduct V (supportedRankSplitVector d)),
      ∀ (q : SymmetricSquare U)
        (z : LinearMap.range (symmetricSquareProduct V (supportedRankSplitVector d))),
        Φ.symm (q, z) = supportedRankSplitSymmetricSquareInclusion d q + (z : SymmetricSquare V) := by
  let j := supportedRankSplitSymmetricSquareInclusion d
  let m := symmetricSquareProduct V (supportedRankSplitVector d)
  let C := supportedRankSplitQuotientMap d
  let R := supportedRankSplitReconstruct d
  have hj (q : SymmetricSquare U) : C (j q) = (q, 0) :=
    supportedRankSplitQuotientMap_inclusion d q
  have hm (v : V) : C (m v) = (0, v) := supportedRankSplitQuotientMap_product d v
  have hji : Function.Injective j := by
    intro q q' h
    have hc := congrArg (fun z ↦ (C z).1) h
    simpa only [hj] using hc
  have hmi : Function.Injective m := by
    intro v v' h
    have hc := congrArg (fun z ↦ (C z).2) h
    simpa only [hm] using hc
  have hcompl : IsCompl (LinearMap.range j) (LinearMap.range m) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro z ⟨⟨q, hq⟩, ⟨v, hv⟩⟩
      change z = 0
      have heq : (q, (0 : V)) = (0, v) :=
        (hj q).symm.trans ((congrArg C (hq.trans hv.symm)).trans (hm v))
      have hq0 : q = 0 := congrArg Prod.fst heq
      rw [← hq, hq0, map_zero]
    · rw [codisjoint_iff_le_sup]
      intro z hz
      exact Submodule.mem_sup.mpr
        ⟨j (C z).1, ⟨(C z).1, rfl⟩, m (C z).2, ⟨(C z).2, rfl⟩,
          supportedRankSplitReconstruct_quotientMap d z⟩
  refine ⟨hji, hmi, hcompl, LinearMap.finrank_range_of_inj hmi, ?_⟩
  let D : SymmetricSquare V ≃ₗ[ℝ] SymmetricSquare U × V :=
    { C with
      invFun := R
      left_inv := supportedRankSplitReconstruct_quotientMap d
      right_inv := fun p ↦ supportedRankSplitQuotientMap_reconstruct d p.1 p.2 }
  let eZ : V ≃ₗ[ℝ] LinearMap.range m := LinearEquiv.ofInjective m hmi
  let Φ := D.trans ((LinearEquiv.refl ℝ (SymmetricSquare U)).prodCongr eZ)
  refine ⟨Φ, ?_⟩
  intro q z
  change j q + m (eZ.symm z) = j q + (z : SymmetricSquare V)
  exact congrArg (fun w : SymmetricSquare V ↦ j q + w)
    (congrArg Subtype.val (eZ.apply_symm_apply z))

end GlobalEmbedding.Paper
