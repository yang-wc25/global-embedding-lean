import Upgrade.RankQFixedPairExtraction
import Upgrade.IncidencePrincipalAssembly
import Upgrade.IncidenceNormalTangent

/-!
# Supported-equation and value directions in the actual ambient incidence

The strong supported-rank packet and the saturation packet are different
subfamilies of one fixed legal-wave list. The accepted two-copy identities
separate their outputs. The actual source derivative then contributes its
tangent directions. In dimension three the result is 3 + 3 + 3 = 9, for the
joint supported-coincidence equation only.
-/

noncomputable section
open Function Module
open scoped BigOperators

namespace GlobalEmbedding.Upgrade

variable {ι E R V : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The exact ambient principal response for the same duplicated labels. -/
def supportedJointPrincipalColumn (T : E →L[ℝ] V)
    (A : ι → R) (v : ι → T.rangeᗮ) (lambda : ι → Fin 2 → ℝ)
    (ij : ι × Fin 2) : R × V :=
  (A ij.1, -((lambda ij.1 ij.2 ^ 2)⁻¹) • (v ij.1 : V))

/-- Joint principal map with the original actual tangent derivative. -/
def supportedJointPrincipalMap (T : E →L[ℝ] V)
    (A : ι → R) (v : ι → T.rangeᗮ) (lambda : ι → Fin 2 → ℝ) :
    (((ι × Fin 2) → ℝ) × E) →L[ℝ] R × V :=
  (incidenceFiniteSynthesis (supportedJointPrincipalColumn T A v lambda)).coprod
    ((0 : E →L[ℝ] R).prod T)

/-- The two selected independent normal families give a lower bound for the
same duplicated packet, with all weights chosen after the original list. -/
theorem supportedJointProjectedPrincipal_rank {q s : ℕ}
    (T : E →L[ℝ] V) (A : ι → R) (v : ι → T.rangeᗮ)
    (lambda : ι → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1)
    (ia : Fin q → ι) (iv : Fin s → ι)
    (hA : LinearIndependent ℝ (A ∘ ia)) (hv : LinearIndependent ℝ (v ∘ iv)) :
    q + s ≤ finrank ℝ (Submodule.span ℝ (Set.range
      (fun ij : ι × Fin 2 ↦ (A ij.1, -((lambda ij.1 ij.2 ^ 2)⁻¹) • v ij.1)))) := by
  let Z := Submodule.span ℝ (Set.range
    (fun ij : ι × Fin 2 ↦ (A ij.1, -((lambda ij.1 ij.2 ^ 2)⁻¹) • v ij.1)))
  let w : Fin (q + s) → R × T.rangeᗮ := fun j ↦
    Sum.elim (fun i ↦ (A (ia i), 0)) (fun i ↦ (0, v (iv i)))
      (finSumFinEquiv.symm j)
  have hw : LinearIndependent ℝ w :=
    (linearIndependent_inl_union_inr' hA hv).comp
      finSumFinEquiv.symm finSumFinEquiv.symm.injective
  have hp := rankQFixedPair_pure_mem A v lambda hlambda hne
  have hm : ∀ j, w j ∈ Z := by
    intro j
    dsimp [w]
    cases finSumFinEquiv.symm j with
    | inl i => exact (hp (ia i)).1
    | inr i => exact (hp (iv i)).2
  have hs : Submodule.span ℝ (Set.range w) ≤ Z := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hm j
  have hdim := Submodule.finrank_mono hs
  rw [finrank_span_eq_card hw, Fintype.card_fin] at hdim
  exact hdim

/-- The actual normal geometry adds the source dimension to the independent
supported-equation and legal-value directions. The desired perturbed
incidence rank is not a premise. -/
theorem supportedJointPrincipalMap_rank {q s : ℕ}
    (T : E →L[ℝ] V) (hT : Injective T) (A : ι → R) (v : ι → T.rangeᗮ)
    (lambda : ι → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1)
    (ia : Fin q → ι) (iv : Fin s → ι)
    (hA : LinearIndependent ℝ (A ∘ ia)) (hv : LinearIndependent ℝ (v ∘ iv)) :
    finrank ℝ E + (q + s) ≤ finrank ℝ (supportedJointPrincipalMap T A v lambda).range := by
  let P := incidenceFiniteSynthesis (supportedJointPrincipalColumn T A v lambda)
  let T0 := (0 : E →L[ℝ] R).prod T
  let Q : R × V →L[ℝ] R × T.rangeᗮ :=
    (ContinuousLinearMap.id ℝ R).prodMap T.rangeᗮ.orthogonalProjectionOnto
  have hT0 : Injective T0 := by
    intro x y h
    exact hT (congrArg Prod.snd h)
  have hQT : Q.comp T0 = 0 := by
    apply ContinuousLinearMap.ext
    intro e
    apply Prod.ext
    · rfl
    · change T.rangeᗮ.orthogonalProjectionOnto (T e) = 0
      exact T.range.orthogonalProjectionOnto_orthogonal_apply_eq_zero ⟨e, rfl⟩
  have hp : (Q.comp P).range = Submodule.span ℝ (Set.range
      (fun ij : ι × Fin 2 ↦ (A ij.1, -((lambda ij.1 ij.2 ^ 2)⁻¹) • v ij.1))) := by
    rw [incidenceFiniteSynthesis_projected_range]
    apply congrArg (Submodule.span ℝ)
    apply congrArg Set.range
    funext ij
    apply Prod.ext
    · rfl
    · change T.rangeᗮ.orthogonalProjectionOnto
        (-((lambda ij.1 ij.2 ^ 2)⁻¹) • (v ij.1 : V)) =
          -((lambda ij.1 ij.2 ^ 2)⁻¹) • v ij.1
      rw [map_smul, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hdim := supportedJointProjectedPrincipal_rank T A v lambda hlambda hne ia iv hA hv
  rw [← hp] at hdim
  exact (Nat.add_le_add_left hdim _).trans (incidencePrincipalCoprod_finrank P T0 Q hT0 hQT)

/-- The actual dimension-three supported-coincidence principal map has rank
at least nine. This says nothing about eliminating all supported kernels. -/
theorem supportedThreeJointPrincipalMap_rank
    (hE : finrank ℝ E = 3)
    (T : E →L[ℝ] V) (hT : Injective T) (A : ι → R) (v : ι → T.rangeᗮ)
    (lambda : ι → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1)
    (ia iv : Fin 3 → ι)
    (hA : LinearIndependent ℝ (A ∘ ia)) (hv : LinearIndependent ℝ (v ∘ iv)) :
    9 ≤ finrank ℝ (supportedJointPrincipalMap T A v lambda).range := by
  simpa [hE] using supportedJointPrincipalMap_rank T hT A v lambda hlambda hne ia iv hA hv

end GlobalEmbedding.Upgrade
