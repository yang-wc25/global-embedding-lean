import GlobalEmbedding.Paper.CollarCKSpatialFormalSolution
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Coefficient-preserving regrouping for the actual CK substitution

Source: Gantumur, notes2, Theorem 18, passage to full time/spatial coefficients.
The finite convolution bijection below generalizes the implementation of Mathlib's
`MvPowerSeries.optionEquivLeft` (Bingyu Xia and Wenrong Zou, Apache 2.0).
The existing single-normal-variable equivalence itself is reused, rather than reproved.
-/

namespace GlobalEmbedding.Paper

open MvPowerSeries
open scoped Classical

section Regroup

variable {σ τ R : Type*} [CommRing R]

/-- Group the actual coefficients by outer variables σ and inner variables τ. -/
noncomputable def collarCKGroup (f : MvPowerSeries (τ ⊕ σ) R) :
    MvPowerSeries σ (MvPowerSeries τ R) :=
  fun d e ↦ coeff (Finsupp.sumElim e d) f

theorem collarCKGroup_coeff (f : MvPowerSeries (τ ⊕ σ) R) (d : σ →₀ ℕ)
    (e : τ →₀ ℕ) : coeff e (coeff d (collarCKGroup f)) =
      coeff (Finsupp.sumElim e d) f := rfl

/-- The inverse coefficient regrouping; no sum or limiting operation changes a coefficient. -/
noncomputable def collarCKUngroup (f : MvPowerSeries σ (MvPowerSeries τ R)) :
    MvPowerSeries (τ ⊕ σ) R :=
  fun t ↦ coeff (Finsupp.comapDomain Sum.inl t Sum.inl_injective.injOn)
    (coeff (Finsupp.comapDomain Sum.inr t Sum.inr_injective.injOn) f)

theorem collarCKUngroup_coeff (f : MvPowerSeries σ (MvPowerSeries τ R))
    (t : τ ⊕ σ →₀ ℕ) : coeff t (collarCKUngroup f) =
      coeff (Finsupp.comapDomain Sum.inl t Sum.inl_injective.injOn)
        (coeff (Finsupp.comapDomain Sum.inr t Sum.inr_injective.injOn) f) := rfl

theorem collarCKGroup_mul (f g : MvPowerSeries (τ ⊕ σ) R) :
    collarCKGroup (f * g) = collarCKGroup f * collarCKGroup g := by
  classical
  ext d e
  simp only [collarCKGroup_coeff, coeff_mul, map_sum, Finset.sum_sigma']
  refine Finset.sum_bij (fun y _ ↦
    ⟨(Finsupp.comapDomain Sum.inr y.1 Sum.inr_injective.injOn,
      Finsupp.comapDomain Sum.inr y.2 Sum.inr_injective.injOn),
     (Finsupp.comapDomain Sum.inl y.1 Sum.inl_injective.injOn,
      Finsupp.comapDomain Sum.inl y.2 Sum.inl_injective.injOn)⟩) ?_ ?_ ?_ ?_
  · intros
    simp_all [Finsupp.ext_iff]
  · intros
    ext t <;> cases t <;> simp_all [Finsupp.ext_iff]
  · rintro ⟨⟨a, b⟩, ⟨c, h⟩⟩ hp
    refine ⟨(Finsupp.sumElim c a, Finsupp.sumElim h b), ?_, ?_⟩
    · simp_all [Finsupp.ext_iff, Sum.forall]
    · simp only [Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inr_sumElim]
  · intros
    simp_all [Finsupp.ext_iff]

/-- The missing multiple-outer-variable ring equivalence, with literal coefficient indexing.
The convolution proof reuses Mathlib's finite antidiagonal-bijection method. -/
noncomputable def collarCKGroupEquiv :
    MvPowerSeries (τ ⊕ σ) R ≃+* MvPowerSeries σ (MvPowerSeries τ R) where
  toFun := collarCKGroup
  invFun := collarCKUngroup
  left_inv f := by
    ext t
    simp only [collarCKUngroup_coeff, collarCKGroup_coeff,
      Finsupp.comapDomain_sumElim_comapDomain]
  right_inv f := by
    ext d e
    simp only [collarCKGroup_coeff, collarCKUngroup_coeff,
      Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inr_sumElim]
  map_mul' := collarCKGroup_mul
  map_add' f g := by ext d e; simp only [collarCKGroup_coeff, map_add]

@[simp]
theorem collarCKGroupEquiv_symm_apply (f : MvPowerSeries σ (MvPowerSeries τ R)) :
    (collarCKGroupEquiv (σ := σ) (τ := τ) (R := R)).symm.toRingHom f =
      collarCKUngroup f := rfl

/-- Spatial inclusion has no coefficient with a nonzero outer multiindex. -/
theorem collarCKRename_inl_coeff (a : MvPowerSeries τ R) (e : τ →₀ ℕ)
    (d : σ →₀ ℕ) :
    coeff (Finsupp.sumElim e d)
      (rename (Function.Embedding.inl : τ ↪ τ ⊕ σ) a) =
        if d = 0 then coeff e a else 0 := by
  classical
  by_cases hd : d = 0
  · subst d
    simpa only [Finsupp.embDomain_inl, ite_true] using
      coeff_embDomain_rename (Function.Embedding.inl : τ ↪ τ ⊕ σ) a e
  · rw [ite_eq_right_iff.mpr (fun h ↦ (hd h).elim)]
    apply coeff_rename_eq_zero
    rintro ⟨b, hb⟩
    have h := congrArg (fun t : τ ⊕ σ →₀ ℕ ↦
      Finsupp.comapDomain Sum.inr t Sum.inr_injective.injOn) hb
    rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_inl,
      Finsupp.comapDomain_inr_sumElim, Finsupp.comapDomain_inr_sumElim] at h
    exact hd h.symm

/-- The other coordinate inclusion has no coefficient with nonzero first multiindex. -/
theorem collarCKRename_inr_coeff (a : MvPowerSeries σ R) (e : τ →₀ ℕ)
    (d : σ →₀ ℕ) :
    coeff (Finsupp.sumElim e d)
      (rename (Function.Embedding.inr : σ ↪ τ ⊕ σ) a) =
        if e = 0 then coeff d a else 0 := by
  classical
  by_cases he : e = 0
  · subst e
    simpa only [Finsupp.embDomain_inr, ite_true] using
      coeff_embDomain_rename (Function.Embedding.inr : σ ↪ τ ⊕ σ) a d
  · rw [ite_eq_right_iff.mpr (fun h ↦ (he h).elim)]
    apply coeff_rename_eq_zero
    rintro ⟨b, hb⟩
    have h := congrArg (fun t : τ ⊕ σ →₀ ℕ ↦
      Finsupp.comapDomain Sum.inl t Sum.inl_injective.injOn) hb
    rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_inr,
      Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inl_sumElim] at h
    exact he h.symm

/-- Regrouped outer constants are the actual spatial-parameter inclusion. -/
theorem collarCKUngroup_C (a : MvPowerSeries τ R) :
    collarCKUngroup (C a : MvPowerSeries σ (MvPowerSeries τ R)) =
      rename (Function.Embedding.inl : τ ↪ τ ⊕ σ) a := by
  apply (collarCKGroupEquiv (σ := σ) (τ := τ) (R := R)).injective
  change collarCKGroupEquiv (collarCKGroupEquiv.symm (C a)) = _
  rw [RingEquiv.apply_symm_apply]
  ext d e
  change coeff e (coeff d (C a)) = coeff e (coeff d
    (collarCKGroup (σ := σ) (τ := τ) (R := R)
      (rename (Function.Embedding.inl : τ ↪ τ ⊕ σ) a)))
  simp only [collarCKGroup_coeff, collarCKRename_inl_coeff, coeff_C]
  split_ifs <;> simp_all

/-- Regrouped genuine outer variables are their full-ring variables. -/
theorem collarCKUngroup_X (s : σ) :
    collarCKUngroup (X s : MvPowerSeries σ (MvPowerSeries τ R)) = X (Sum.inr s) := by
  apply (collarCKGroupEquiv (σ := σ) (τ := τ) (R := R)).injective
  change collarCKGroupEquiv (collarCKGroupEquiv.symm (X s)) = _
  rw [RingEquiv.apply_symm_apply]
  ext d e
  change coeff e (coeff d (X s : MvPowerSeries σ (MvPowerSeries τ R))) =
    coeff e (coeff d (collarCKGroup (X (Sum.inr s) : MvPowerSeries (τ ⊕ σ) R)))
  simp only [collarCKGroup_coeff, coeff_X]
  have hs : Finsupp.sumElim e d = Finsupp.single (Sum.inr s) 1 ↔
      e = 0 ∧ d = Finsupp.single s 1 := by
    rw [← Finsupp.sumElim_zero_single]
    constructor
    · intro h
      constructor
      · simpa only [Finsupp.comapDomain_inl_sumElim] using
          congrArg (fun t ↦ Finsupp.comapDomain Sum.inl t Sum.inl_injective.injOn) h
      · simpa only [Finsupp.comapDomain_inr_sumElim] using
          congrArg (fun t ↦ Finsupp.comapDomain Sum.inr t Sum.inr_injective.injOn) h
    · rintro ⟨rfl, rfl⟩
      rfl
  simp only [hs]
  split_ifs <;> simp_all [coeff_one]

end Regroup

section Evaluation

open scoped MvPowerSeries.WithPiTopology

variable {σ τ R : Type*} [CommRing R] [UniformSpace R] [DiscreteUniformity R]

/-- Native evaluation with a discrete spatial coefficient ring; the output retains its
full-variable coefficient topology. The topology is an internal construction detail. -/
noncomputable def collarCKGroupedEval (f : MvPowerSeries σ (MvPowerSeries τ R)) :
    MvPowerSeries (τ ⊕ σ) R := by
  letI : UniformSpace (MvPowerSeries τ R) := ⊥
  letI : TopologicalSpace (MvPowerSeries τ R) := ⊥
  exact eval₂ (rename (Function.Embedding.inl : τ ↪ τ ⊕ σ)).toRingHom
    (fun s : σ ↦ X (Sum.inr s)) f

/-- Native polynomial-density evaluation identifies the regrouping, with discrete spatial
coefficient topology used only inside this proof of a formal algebraic identity. -/
theorem collarCKUngroup_eq_eval₂ (f : MvPowerSeries σ (MvPowerSeries τ R)) :
    collarCKUngroup f = collarCKGroupedEval f := by
  unfold collarCKGroupedEval
  let : UniformSpace (MvPowerSeries τ R) := ⊥
  let : TopologicalSpace (MvPowerSeries τ R) := ⊥
  let : DiscreteTopology (MvPowerSeries τ R) := ⟨rfl⟩
  let φ := (rename (Function.Embedding.inl : τ ↪ τ ⊕ σ) (R := R)).toRingHom
  have hφ : Continuous φ := continuous_of_discreteTopology
  have hslots : HasEval (fun s : σ ↦ (X (Sum.inr s) : MvPowerSeries (τ ⊕ σ) R)) :=
    (HasSubst.X_comp (Function.Embedding.inr : σ ↪ τ ⊕ σ)).hasEval
  have hcont : Continuous (collarCKUngroup (σ := σ) (τ := τ) (R := R)) := by
    apply continuous_pi
    intro t
    exact (continuous_of_discreteTopology : Continuous
      (coeff (Finsupp.comapDomain Sum.inl t Sum.inl_injective.injOn) :
        MvPowerSeries τ R → R)).comp
      (WithPiTopology.continuous_coeff (MvPowerSeries τ R)
        (Finsupp.comapDomain Sum.inr t Sum.inr_injective.injOn))
  have hpoly : ∀ p : MvPolynomial σ (MvPowerSeries τ R),
      collarCKUngroup (p : MvPowerSeries σ (MvPowerSeries τ R)) =
        MvPolynomial.eval₂ φ (fun s : σ ↦ X (Sum.inr s)) p := by
    have h := MvPolynomial.ringHom_ext
      (f := (collarCKGroupEquiv (σ := σ) (τ := τ) (R := R)).symm.toRingHom.comp
        MvPolynomial.coeToMvPowerSeries.ringHom)
      (g := MvPolynomial.eval₂Hom φ (fun s : σ ↦ X (Sum.inr s)))
      (fun a ↦ by
        simpa only [RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
          MvPolynomial.coe_C,
          MvPolynomial.eval₂Hom_C, collarCKGroupEquiv_symm_apply, φ,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
          collarCKUngroup_C (σ := σ) a)
      (fun s ↦ by
        simpa only [RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
          MvPolynomial.coe_X, MvPolynomial.eval₂Hom_X',
          collarCKGroupEquiv_symm_apply] using
          collarCKUngroup_X (τ := τ) (R := R) s)
    intro p
    exact DFunLike.congr_fun h p
  exact congrFun (eval₂_unique hφ hslots hcont hpoly) f

end Evaluation

open scoped MvPowerSeries.WithPiTopology

variable {n m : ℕ}

/-- Index transport to the native one-normal-variable equivalence. -/
def collarCKTimeIndexEquiv (n : ℕ) : CollarCKFullIndex n ≃ Option (Fin n) where
  toFun := Sum.elim (fun _ ↦ none) some
  invFun := fun s ↦ match s with
    | none => Sum.inl ()
    | some i => Sum.inr i
  left_inv s := by rcases s with ⟨⟩ | i <;> rfl
  right_inv s := by cases s <;> rfl

/-- Reuse the native single-normal-variable ring equivalence with the accepted index order. -/
noncomputable def collarCKNormalEquiv (n : ℕ) :
    MvPowerSeries (CollarCKFullIndex n) ℝ ≃+* PowerSeries (CollarCKSpatial n) :=
  ((renameEquiv ℝ (collarCKTimeIndexEquiv n)).trans
    (optionEquivLeft (Fin n) ℝ)).toRingEquiv

theorem collarCKNormalEquiv_coeff (f : MvPowerSeries (CollarCKFullIndex n) ℝ)
    (k : ℕ) (β : Fin n →₀ ℕ) :
    coeff β (PowerSeries.coeff k (collarCKNormalEquiv n f)) =
      coeff (collarCKMultiIndex k β) f := by
  have ht : Finsupp.embDomain (collarCKTimeIndexEquiv n).toEmbedding
      (collarCKMultiIndex k β) = β.optionElim k := by
    ext s
    cases s with
    | none =>
      change Finsupp.embDomain (collarCKTimeIndexEquiv n).toEmbedding
        (collarCKMultiIndex k β) ((collarCKTimeIndexEquiv n).toEmbedding (Sum.inl ())) = _
      simp only [Finsupp.embDomain_apply_self,
        collarCKMultiIndex_time, Finsupp.optionElim_apply_none]
    | some i =>
      change Finsupp.embDomain (collarCKTimeIndexEquiv n).toEmbedding
        (collarCKMultiIndex k β) ((collarCKTimeIndexEquiv n).toEmbedding (Sum.inr i)) = _
      rw [Finsupp.embDomain_apply_self]
      simp only [collarCKMultiIndex, Finsupp.sumElim_inr, Finsupp.optionElim_apply_some]
  change coeff β (PowerSeries.coeff k
    (optionEquivLeft (Fin n) ℝ (rename (collarCKTimeIndexEquiv n) f))) = _
  rw [coeff_coeff_optionEquivLeft, ← ht]
  exact coeff_embDomain_rename (collarCKTimeIndexEquiv n).toEmbedding f _

/-- The native inverse is exactly the accepted scalar component flattening. -/
theorem collarCKNormalEquiv_symm_component (u : CollarCKVector n m) (j : Fin m) :
    (collarCKNormalEquiv n).symm (collarCKComponent u j) = collarCKFlatten u j := by
  apply (collarCKNormalEquiv n).injective
  rw [RingEquiv.apply_symm_apply]
  apply PowerSeries.ext
  intro k
  apply MvPowerSeries.ext
  intro β
  simp only [collarCKComponent_coeff, collarCKNormalEquiv_coeff,
    collarCKFlatten_coeff_multiIndex, collarCKCoeff]

theorem collarCKNormalEquiv_symm_coeff (p : PowerSeries (CollarCKSpatial n))
    (k : ℕ) (β : Fin n →₀ ℕ) :
    coeff (collarCKMultiIndex k β) ((collarCKNormalEquiv n).symm p) =
      coeff β (PowerSeries.coeff k p) := by
  have h := collarCKNormalEquiv_coeff ((collarCKNormalEquiv n).symm p) k β
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

theorem collarCKNormalEquiv_symm_coeff_full (p : PowerSeries (CollarCKSpatial n))
    (t : CollarCKFullIndex n →₀ ℕ) :
    coeff t ((collarCKNormalEquiv n).symm p) =
      coeff (collarCKSpatialIndex t) (PowerSeries.coeff (t (Sum.inl ())) p) := by
  simpa only [collarCKMultiIndex_split] using
    collarCKNormalEquiv_symm_coeff p (t (Sum.inl ())) (collarCKSpatialIndex t)

/-- The native inverse preserves the actual spatial parameter inclusion. -/
theorem collarCKNormalEquiv_symm_C (a : CollarCKSpatial n) :
    (collarCKNormalEquiv n).symm (PowerSeries.C a) =
      rename (Function.Embedding.inr : Fin n ↪ CollarCKFullIndex n) a := by
  apply MvPowerSeries.ext
  intro t
  rw [← collarCKMultiIndex_split t]
  rw [collarCKNormalEquiv_symm_coeff]
  simp only [collarCKMultiIndex, collarCKRename_inr_coeff, PowerSeries.coeff_C,
    Finsupp.single_eq_zero]
  split_ifs <;> simp_all

theorem collarCKNormalEquiv_symm_X :
    (collarCKNormalEquiv n).symm PowerSeries.X = X (Sum.inl ()) := by
  apply (collarCKNormalEquiv n).injective
  rw [RingEquiv.apply_symm_apply]
  change PowerSeries.X = optionEquivLeft (Fin n) ℝ
    (rename (collarCKTimeIndexEquiv n) (X (Sum.inl ())))
  rw [rename_X]
  exact optionEquivLeft_X_none.symm

/-- Zero normal initial series implies zero total constant coefficient after rearrangement. -/
theorem collarCKNormalEquiv_symm_constantCoeff (p : PowerSeries (CollarCKSpatial n))
    (hp : PowerSeries.constantCoeff p = 0) :
    constantCoeff ((collarCKNormalEquiv n).symm p) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, collarCKNormalEquiv_symm_coeff_full]
  simp only [Finsupp.zero_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, map_zero]

/-- Include spatial parameters and flatten the actual normal substitution slots. -/
noncomputable def collarCKFullSubstitutionSlots {σ : Type*}
    (p : σ → PowerSeries (CollarCKSpatial n)) :
    Fin n ⊕ σ → MvPowerSeries (CollarCKFullIndex n) ℝ :=
  Sum.elim (fun i ↦ X (Sum.inr i)) (fun s ↦ (collarCKNormalEquiv n).symm (p s))

/-- These are lawful full-origin slots. Only the actual normal input slots, not a scalar
majorant's normal initial series, are assumed to have zero normal constant coefficient. -/
theorem collarCKFullSubstitutionSlots_hasSubst {σ : Type*} [Finite σ]
    (p : σ → PowerSeries (CollarCKSpatial n))
    (hp : ∀ s, PowerSeries.constantCoeff (p s) = 0) :
    HasSubst (collarCKFullSubstitutionSlots p) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (i | s)
  · exact constantCoeff_X _
  · exact collarCKNormalEquiv_symm_constantCoeff (p s) (hp s)

/-- Full-origin substitution preserves the spatial-parameter inclusion. -/
theorem collarCKFullSubstitutionSlots_spatial {σ : Type*} [Finite σ]
    (p : σ → PowerSeries (CollarCKSpatial n))
    (hp : ∀ s, PowerSeries.constantCoeff (p s) = 0) (a : CollarCKSpatial n) :
    subst (collarCKFullSubstitutionSlots p)
      (rename (Function.Embedding.inl : Fin n ↪ Fin n ⊕ σ) a) =
        (collarCKNormalEquiv n).symm (PowerSeries.C a) := by
  rw [rename_eq_subst,
    subst_comp_subst_apply (HasSubst.X_comp (Function.Embedding.inl : Fin n ↪ Fin n ⊕ σ))
      (collarCKFullSubstitutionSlots_hasSubst p hp)]
  simp only [Function.comp_apply, subst_X (collarCKFullSubstitutionSlots_hasSubst p hp)]
  rw [collarCKNormalEquiv_symm_C, rename_eq_subst]
  rfl

/-- Exact nonlinear compatibility for arbitrary finite zero-normal-initial slots over the
actual spatial coefficient ring. The proof uses native continuous evaluation composition,
with discrete coefficient topologies internal to the algebraic argument. -/
theorem collarCKFlattenSubstitution_general {σ : Type*} [Finite σ]
    (G : MvPowerSeries σ (CollarCKSpatial n))
    (p : σ → PowerSeries (CollarCKSpatial n))
    (hp : ∀ s, PowerSeries.constantCoeff (p s) = 0) :
    (collarCKNormalEquiv n).symm (subst p G) =
      subst (collarCKFullSubstitutionSlots p) (collarCKUngroup G) := by
  let : UniformSpace ℝ := ⊥
  let : UniformSpace (CollarCKSpatial n) := ⊥
  let : TopologicalSpace (CollarCKSpatial n) := ⊥
  let : DiscreteTopology (CollarCKSpatial n) := ⟨rfl⟩
  let ε := (collarCKNormalEquiv n).symm.toRingHom
  let b := collarCKFullSubstitutionSlots p
  have hb : HasSubst b := collarCKFullSubstitutionSlots_hasSubst p hp
  let η := (substAlgHom (R := ℝ) hb).toRingHom
  let φ := (rename (Function.Embedding.inl : Fin n ↪ Fin n ⊕ σ) (R := ℝ)).toRingHom
  have hε : Continuous ε := by
    change Continuous (fun v ↦ (collarCKNormalEquiv n).symm v)
    apply continuous_pi
    intro t
    change Continuous (fun v ↦ coeff t ((collarCKNormalEquiv n).symm v))
    simp only [collarCKNormalEquiv_symm_coeff_full]
    exact (continuous_of_discreteTopology : Continuous
      (coeff (collarCKSpatialIndex t) : CollarCKSpatial n → ℝ)).comp
      (PowerSeries.WithPiTopology.continuous_coeff (CollarCKSpatial n) (t (Sum.inl ())))
  have hη : Continuous η := by
    simpa only [η, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom] using
      continuous_subst (R := ℝ) hb
  have hφ : Continuous φ := continuous_of_discreteTopology
  have hp' : HasSubst p := hasSubst_of_constantCoeff_zero hp
  have hleft : ε (subst p G) =
      eval₂ (ε.comp (PowerSeries.C (R := CollarCKSpatial n))) (ε ∘ p) G := by
    rw [subst_eq_eval₂]
    exact congrFun (comp_eval₂
      (continuous_algebraMap (CollarCKSpatial n) (PowerSeries (CollarCKSpatial n)))
      hp'.hasEval hε) G
  have hright : η (collarCKUngroup G) =
      eval₂ (η.comp φ) (η ∘ (fun s : σ ↦ (X (Sum.inr s) : MvPowerSeries (Fin n ⊕ σ) ℝ)))
        G := by
    rw [collarCKUngroup_eq_eval₂]
    unfold collarCKGroupedEval
    exact congrFun (comp_eval₂ hφ
      (HasSubst.X_comp (Function.Embedding.inr : σ ↪ Fin n ⊕ σ)).hasEval hη) G
  have hcoeff : η.comp φ = ε.comp (PowerSeries.C (R := CollarCKSpatial n)) := by
    apply RingHom.ext
    intro a
    simpa only [RingHom.comp_apply, η, φ, ε, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, coe_substAlgHom, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom] using collarCKFullSubstitutionSlots_spatial p hp a
  have hslots : η ∘ (fun s : σ ↦ (X (Sum.inr s) : MvPowerSeries (Fin n ⊕ σ) ℝ)) =
      ε ∘ p := by
    funext s
    simpa only [Function.comp_apply, η, ε, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, coe_substAlgHom, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, b, collarCKFullSubstitutionSlots, Sum.elim_inr] using
      subst_X hb (Sum.inr s)
  rw [hcoeff, hslots] at hright
  simpa only [ε, η, b, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using hleft.trans hright.symm

/-- The same actual RHS with spatial and nonlinear-slot indices regrouped into one ring. -/
noncomputable def collarCKFullRHS (G : CollarCKRHS n m) (j : Fin m) :
    MvPowerSeries (Fin n ⊕ CollarCKSlot n m) ℝ :=
  collarCKUngroup (G j)

/-- Every coefficient is retained with the same spatial and nonlinear-slot multiplicities. -/
theorem collarCKFullRHS_coeff (G : CollarCKRHS n m) (j : Fin m)
    (β : Fin n →₀ ℕ) (d : CollarCKSlot n m →₀ ℕ) :
    coeff (Finsupp.sumElim β d) (collarCKFullRHS G j) = coeff β (coeff d (G j)) := by
  simp only [collarCKFullRHS, collarCKUngroup_coeff, Finsupp.comapDomain_inl_sumElim,
    Finsupp.comapDomain_inr_sumElim]

/-- Identify any actual analytic Taylor packaging with this same coefficient regrouping. -/
theorem collarCKFullRHS_eq_of_coeff (G : CollarCKRHS n m)
    (H : Fin m → MvPowerSeries (Fin n ⊕ CollarCKSlot n m) ℝ)
    (hH : ∀ j β d, coeff (Finsupp.sumElim β d) (H j) = coeff β (coeff d (G j)))
    (j : Fin m) : collarCKFullRHS G j = H j := by
  ext t
  rw [← Finsupp.comapDomain_sumElim_comapDomain t, collarCKFullRHS_coeff, hH]

/-- The actual full nonlinear slots of the same canonical CK formal series. -/
noncomputable def collarCKFullSlots (u : CollarCKVector n m) :
    Fin n ⊕ CollarCKSlot n m → MvPowerSeries (CollarCKFullIndex n) ℝ :=
  collarCKFullSubstitutionSlots (collarCKSlots u)

theorem collarCKFullSlots_spatial (u : CollarCKVector n m) (i : Fin n) :
    collarCKFullSlots u (Sum.inl i) = X (Sum.inr i) := rfl

theorem collarCKFullSlots_time (u : CollarCKVector n m) :
    collarCKFullSlots u (Sum.inr (Sum.inl ())) = X (Sum.inl ()) :=
  collarCKNormalEquiv_symm_X

theorem collarCKFullSlots_value (u : CollarCKVector n m) (j : Fin m) :
    collarCKFullSlots u (Sum.inr (Sum.inr (Sum.inl j))) = collarCKFlatten u j :=
  collarCKNormalEquiv_symm_component u j

theorem collarCKFullSlots_gradient (u : CollarCKVector n m) (i : Fin n) (j : Fin m) :
    collarCKFullSlots u (Sum.inr (Sum.inr (Sum.inr (i, j)))) =
      pderiv (Sum.inr i) (collarCKFlatten u j) :=
  (collarCKNormalEquiv_symm_component (collarCKSpatialDeriv i u) j).trans
    (collarCKFlatten_spatialDeriv u j i)

/-- Genuine full-total `HasSubst`, derived from the actual initial hypersurface equation. -/
theorem collarCKFullSlots_hasSubst (u : CollarCKVector n m)
    (hu : PowerSeries.constantCoeff u = 0) : HasSubst (collarCKFullSlots u) :=
  collarCKFullSubstitutionSlots_hasSubst (collarCKSlots u) (collarCKSlots_constantCoeff u hu)

/-- Actual nonlinear flattening compatibility for the CK system, with spatial parameters
included as their genuine coordinate variables. No compatibility premise is supplied.

Source: Gantumur, notes2, Theorem 18, coefficient-majorant passage. The exact coefficient
regrouping is a ring map, and agrees with native evaluation by polynomial density. Composing
native evaluations identifies normal substitution followed by the native normal-series ring
equivalence with the genuine full-variable substitution. Constants map to the actual spatial
inclusion and every nonlinear slot maps to the same actual flattened series. Zero normal
initial data supplies lawful `HasSubst` on both sides. No convergence is asserted. -/
theorem collarCKFlattenSubstitution (G : CollarCKRHS n m) (u : CollarCKVector n m)
    (hu : PowerSeries.constantCoeff u = 0) (j : Fin m) :
    collarCKFlatten (collarCKSubstitutedRHS G u) j =
      subst (collarCKFullSlots u) (collarCKFullRHS G j) := by
  have hcomponent : collarCKComponent (collarCKSubstitutedRHS G u) j =
      subst (collarCKSlots u) (G j) := by
    apply PowerSeries.ext
    intro k
    simp only [collarCKComponent_coeff, collarCKSubstitutedRHS_coeff]
  rw [← collarCKNormalEquiv_symm_component, hcomponent]
  exact collarCKFlattenSubstitution_general (G j) (collarCKSlots u)
    (collarCKSlots_constantCoeff u hu)

/-- The same genuine normal PDE, now as an equation in the full time/spatial formal ring. -/
theorem collarCKFullFormalEquation (G : CollarCKRHS n m) (u : CollarCKVector n m)
    (hu : PowerSeries.constantCoeff u = 0)
    (hdu : PowerSeries.derivative u = collarCKSubstitutedRHS G u) (j : Fin m) :
    pderiv (Sum.inl ()) (collarCKFlatten u j) =
      subst (collarCKFullSlots u) (collarCKFullRHS G j) := by
  rw [← collarCKFlatten_normalDeriv, hdu]
  exact collarCKFlattenSubstitution G u hu j

/-- The actual chosen canonical solution satisfies the actual full-variable PDE internally. -/
theorem collarCKFormalSolution_fullEquation (G : CollarCKRHS n m) (j : Fin m) :
    pderiv (Sum.inl ()) (collarCKFlatten (collarCKFormalSolution G) j) =
      subst (collarCKFullSlots (collarCKFormalSolution G)) (collarCKFullRHS G j) :=
  collarCKFullFormalEquation G (collarCKFormalSolution G)
    (collarCKFormalSolution_spec G).1 (collarCKFormalSolution_spec G).2 j

end GlobalEmbedding.Paper
