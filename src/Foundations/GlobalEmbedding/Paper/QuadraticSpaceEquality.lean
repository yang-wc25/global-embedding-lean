import GlobalEmbedding.Paper.QuadraticSpaceDimension
import GlobalEmbedding.Paper.PointwiseDependentCommonLine
import GlobalEmbedding.Paper.QuadraticSpaceEqualityGeometry

/-! Equality classification for the full real quadratic-space dimension lemma,
revised1816–1843. The original binary quotient dictionary remains W2's canonical API. -/

noncomputable section
open Module
namespace GlobalEmbedding.Paper
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Equality in the sharp dimension bound identifies the actual evaluation
kernel with ALL selfadjoint operators supported on E. This is a conclusion,
not an assumed completeness of the kernel. Source: revised1816–1819. -/
theorem quadraticSpace_equality_kernel_supported
    (P : Submodule ℝ (V →L[ℝ] V))
    (hP : ∀ Q ∈ P, Q.toLinearMap.IsSymmetric) (x₀ : V)
    (hmax : ∀ x : V,
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤
        finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap))
    (Q₀ : V →L[ℝ] V) (hQ₀ : Q₀ ∈ P) (hquad : inner ℝ (Q₀ x₀) x₀ ≠ 0)
    (heq : finrank ℝ P =
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap) *
        (finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap) + 1) / 2) :
    ((quadraticSpaceEvaluation P x₀).ker.map P.subtype) =
      quadraticSpaceSupportedOperators
        (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap ⊓ (ℝ ∙ x₀)ᗮ) := by
  let T := (quadraticSpaceEvaluation P x₀).toLinearMap
  let U := T.range
  let E := U ⊓ (ℝ ∙ x₀)ᗮ
  let K := T.ker
  let H := K.map P.subtype
  have : FiniteDimensional ℝ (V →L[ℝ] V) := inferInstance
  have : FiniteDimensional ℝ P := inferInstance
  have : FiniteDimensional ℝ K := inferInstance
  have hle : H ≤ quadraticSpaceSupportedOperators E := by
    rintro Q ⟨a, ha, rfl⟩
    have hz : (a : V →L[ℝ] V) x₀ = 0 := ha
    have hr := quadraticSpace_maximal_kernel_range P x₀ hmax
      (a : V →L[ℝ] V) a.property hz
    exact ⟨hP a a.property,
      quadraticSpace_kernel_range_supported a (hP a a.property) hz U hr⟩
  have hE : finrank ℝ E + 1 = finrank ℝ U :=
    quadraticSpace_support_hyperplane_finrank U x₀ ⟨Q₀ x₀, ⟨⟨Q₀, hQ₀⟩, rfl⟩⟩ hquad
  have htri : finrank ℝ U + finrank ℝ E * (finrank ℝ E + 1) / 2 =
      finrank ℝ U * (finrank ℝ U + 1) / 2 := by
    rw [← hE]
    simpa [Nat.choose_two_right, Nat.mul_comm, Nat.add_assoc] using
      (Nat.choose_succ_succ' (finrank ℝ E + 1) 1).symm
  have hnull : finrank ℝ U + finrank ℝ K = finrank ℝ P :=
    T.finrank_range_add_finrank_ker
  have hK : finrank ℝ K = finrank ℝ E * (finrank ℝ E + 1) / 2 := by
    change finrank ℝ P = finrank ℝ U * (finrank ℝ U + 1) / 2 at heq
    omega
  have hH : finrank ℝ H = finrank ℝ K := Submodule.finrank_map_subtype_eq P K
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [hH, hK]
  exact quadraticSpaceSupportedOperators_finrank_le E

/-- Projecting a real R containing E to E-perp loses exactly dim E. In the
codimension-at-most-one case the actual projected image has rank at most one.
This supplies the genuine projected evaluation-rank estimate in revised1820–1825. -/
theorem quadraticSpace_projected_finrank_le_one
    (E R : Submodule ℝ V) (hER : E ≤ R)
    (hdim : finrank ℝ R ≤ finrank ℝ E + 1) :
    finrank ℝ (LinearMap.range ((Eᗮ.starProjection).toLinearMap.comp R.subtype)) ≤ 1 := by
  let g := (Eᗮ.starProjection).toLinearMap.comp R.subtype
  have hk : g.ker = E.comap R.subtype := by
    simp only [g, LinearMap.ker_comp, Submodule.ker_starProjection,
      Submodule.orthogonal_orthogonal]
  have hkd : finrank ℝ g.ker = finrank ℝ E := by
    rw [hk]
    exact (Submodule.comapSubtypeEquivOfLe hER).finrank_eq
  have hnull := g.finrank_range_add_finrank_ker
  rw [hkd] at hnull
  change finrank ℝ g.range ≤ 1
  omega

/-- The actual projection of operator values onto E-perp, as a native linear
map between existing endomorphism spaces. -/
def quadraticSpaceProjectionMap (E : Submodule ℝ V) :
    (V →L[ℝ] V) →ₗ[ℝ] (V →ₗ[ℝ] V) where
  toFun Q := (Eᗮ.starProjection).toLinearMap.comp Q.toLinearMap
  map_add' A B := by ext v; simp; abel
  map_smul' a A := by ext v; simp

/-- Projection onto E-perp has exactly the same operator-space rank as the
base evaluation. The equality of the two actual kernels is proved internally.
Source: revised1817–1820. -/
theorem quadraticSpace_projected_space_finrank
    (P : Submodule ℝ (V →L[ℝ] V))
    (hP : ∀ Q ∈ P, Q.toLinearMap.IsSymmetric) (x₀ : V)
    (hmax : ∀ x : V,
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤
        finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap)) :
    finrank ℝ (LinearMap.range ((quadraticSpaceProjectionMap
      (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap ⊓
        (ℝ ∙ x₀)ᗮ)).comp P.subtype)) =
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap) := by
  let T := (quadraticSpaceEvaluation P x₀).toLinearMap
  let U := T.range
  let E := U ⊓ (ℝ ∙ x₀)ᗮ
  let F := (quadraticSpaceProjectionMap E).comp P.subtype
  have : FiniteDimensional ℝ (V →L[ℝ] V) := inferInstance
  have : FiniteDimensional ℝ P := inferInstance
  have hker : F.ker = T.ker := by
    ext Q
    constructor
    · intro hQ
      have hQ' : F Q = 0 := hQ
      have hr : LinearMap.range (Q : V →L[ℝ] V).toLinearMap ≤ E := by
        rintro _ ⟨v, rfl⟩
        have hz : Eᗮ.starProjection ((Q : V →L[ℝ] V) v) = 0 :=
          LinearMap.congr_fun hQ' v
        have hm : (Q : V →L[ℝ] V) v ∈ Eᗮ.starProjection.ker := hz
        rw [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal] at hm
        exact hm
      have hx : x₀ ∈ Eᗮ := by
        apply (E.mem_orthogonal x₀).mpr
        intro v hv
        simpa only [real_inner_comm] using
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv.2
      exact quadraticSpace_kills_orthogonal Q (hP Q Q.property) E hr hx
    · intro hQ
      have hz : (Q : V →L[ℝ] V) x₀ = 0 := hQ
      have hr := quadraticSpace_maximal_kernel_range P x₀ hmax
        (Q : V →L[ℝ] V) Q.property hz
      have hs := quadraticSpace_kernel_range_supported Q (hP Q Q.property) hz U hr
      change F Q = 0
      ext v
      change (Q : V →L[ℝ] V) v ∈ Eᗮ.starProjection.ker
      simpa only [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal] using hs v
  have hF := F.finrank_range_add_finrank_ker
  have hT := T.finrank_range_add_finrank_ker
  rw [hker] at hF
  exact Nat.add_right_cancel (hF.trans hT.symm)

/-- Once the equality kernel has supplied every E-supported operator, projected
evaluations are genuinely dependent on the nonorthogonal open set. No desired
rank bound is postulated for the projection; it is derived by rank-nullity.
Source: revised1820–1825. -/
theorem quadraticSpace_projected_evaluation_dependent
    (E : Submodule ℝ V) (P : Submodule ℝ (V →L[ℝ] V))
    (hsub : quadraticSpaceSupportedOperators E ≤ P)
    (hmax : ∀ x : V, finrank ℝ
      (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤ finrank ℝ E + 1) :
    ∀ A ∈ LinearMap.range ((quadraticSpaceProjectionMap E).comp P.subtype),
    ∀ B ∈ LinearMap.range ((quadraticSpaceProjectionMap E).comp P.subtype),
    ∀ x, x ∉ Eᗮ → ¬ LinearIndependent ℝ ![A x, B x] := by
  rintro A ⟨Q, hQ⟩ B ⟨S, hS⟩ x hx hli
  let R := LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap
  have hER : E ≤ R := by
    intro w hw
    obtain ⟨C, hCsym, hCrange, hCx⟩ :=
      quadraticSpace_supported_evaluation_surjective E x hx w hw
    have hCP : C ∈ P := hsub ⟨hCsym, hCrange⟩
    exact ⟨⟨C, hCP⟩, hCx⟩
  let g := (Eᗮ.starProjection).toLinearMap.comp R.subtype
  have hb : finrank ℝ g.range ≤ 1 :=
    quadraticSpace_projected_finrank_le_one E R hER (hmax x)
  have hAx : A x ∈ g.range := by
    refine ⟨⟨(Q : V →L[ℝ] V) x, ⟨Q, rfl⟩⟩, ?_⟩
    exact congrArg (fun C : V →ₗ[ℝ] V ↦ C x) hQ
  have hBx : B x ∈ g.range := by
    refine ⟨⟨(S : V →L[ℝ] V) x, ⟨S, rfl⟩⟩, ?_⟩
    exact congrArg (fun C : V →ₗ[ℝ] V ↦ C x) hS
  have hmem : ∀ i : Fin 2, (![A x, B x] : Fin 2 → V) i ∈ g.range := by
    intro i
    fin_cases i
    · exact hAx
    · exact hBx
  have : FiniteDimensional ℝ g.range := inferInstance
  have hli' : LinearIndependent ℝ
      (fun i : Fin 2 ↦ (⟨![A x, B x] i, hmem i⟩ : g.range)) :=
    hli.codRestrict g.range hmem
  have htwo : 2 ≤ finrank ℝ g.range := by simpa using hli'.fintype_card_le_finrank
  omega

/-- The projected operator family is pointwise dependent EVERYWHERE. The
complement of E-perp is used only to prove the rank estimate; native openness
extends that estimate to all vectors, as required by the common-line theorem.
Source: revised1825–1827. -/
theorem quadraticSpace_projected_evaluation_dependent_everywhere
    (E : Submodule ℝ V) (hE : E ≠ ⊥) (P : Submodule ℝ (V →L[ℝ] V))
    (hsub : quadraticSpaceSupportedOperators E ≤ P)
    (hmax : ∀ x : V, finrank ℝ
      (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤ finrank ℝ E + 1) :
    ∀ A ∈ LinearMap.range ((quadraticSpaceProjectionMap E).comp P.subtype),
    ∀ B ∈ LinearMap.range ((quadraticSpaceProjectionMap E).comp P.subtype),
    ∀ x, ¬ LinearIndependent ℝ ![A x, B x] := by
  intro A hA B hB
  exact quadraticSpace_pointwise_dependent_extension E hE
    A.toContinuousLinearMap B.toContinuousLinearMap
    (quadraticSpace_projected_evaluation_dependent E P hsub hmax A hA B hB)

/-- FULL d>=2 equality classification for the real quadratic-space bound.
The two rank clauses say exactly that d is the maximum actual evaluation rank.
No common support, good point, complete kernel or projected rank is a hypothesis.
Source: revised lemma1779–1787 and equality proof1816–1843. -/
theorem quadraticSpace_equality_classification
    (P : Submodule ℝ (V →L[ℝ] V))
    (hP : ∀ Q ∈ P, Q.toLinearMap.IsSymmetric) (d : ℕ) (hd : 2 ≤ d)
    (hmax : ∀ x : V,
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤ d)
    (hattain : ∃ x : V,
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) = d)
    (heq : finrank ℝ P = d * (d + 1) / 2) :
    ∃ U : Submodule ℝ V, finrank ℝ U = d ∧ P = quadraticSpaceSupportedOperators U := by
  have hp : 6 ≤ d * (d + 1) := Nat.mul_le_mul hd (Nat.add_le_add_right hd 1)
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at heq
    omega
  obtain ⟨x₀, hmax₀, Q₀, hQ₀, hquad⟩ :=
    quadraticSpace_exists_maximal_nonorthogonal P hP hPne
  let T := (quadraticSpaceEvaluation P x₀).toLinearMap
  let U₀ := T.range
  let E := U₀ ⊓ (ℝ ∙ x₀)ᗮ
  let F := (quadraticSpaceProjectionMap E).comp P.subtype
  let L := F.range
  have : FiniteDimensional ℝ (V →L[ℝ] V) := inferInstance
  have : FiniteDimensional ℝ P := inferInstance
  have hUdim : finrank ℝ U₀ = d := by
    obtain ⟨x, hx⟩ := hattain
    apply Nat.le_antisymm (hmax x₀)
    have hh := hmax₀ x
    rw [hx] at hh
    exact hh
  have hEdim : finrank ℝ E + 1 = finrank ℝ U₀ :=
    quadraticSpace_support_hyperplane_finrank U₀ x₀ ⟨Q₀ x₀, ⟨⟨Q₀, hQ₀⟩, rfl⟩⟩ hquad
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot, hUdim] at hEdim
    omega
  have heq₀ : finrank ℝ P = finrank ℝ U₀ * (finrank ℝ U₀ + 1) / 2 := by
    rw [hUdim]
    exact heq
  have hkernel := quadraticSpace_equality_kernel_supported P hP x₀ hmax₀ Q₀ hQ₀ hquad heq₀
  have hsub : quadraticSpaceSupportedOperators E ≤ P := by
    rw [← hkernel]
    rintro _ ⟨Q, _, rfl⟩
    exact Q.property
  have hLdim : finrank ℝ L = finrank ℝ U₀ :=
    quadraticSpace_projected_space_finrank P hP x₀ hmax₀
  have hLtwo : 2 ≤ finrank ℝ L := by rw [hLdim, hUdim]; exact hd
  have hmaxE (x : V) : finrank ℝ
      (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤ finrank ℝ E + 1 := by
    rw [hEdim]
    exact hmax₀ x
  have hdep : ∀ A ∈ L, ∀ B ∈ L, ∀ x, ¬ LinearIndependent ℝ ![A x, B x] :=
    quadraticSpace_projected_evaluation_dependent_everywhere E hEne P hsub hmaxE
  obtain ⟨f, hf, hline⟩ := quadraticSpace_common_image_line L hLtwo hdep
  have hfE : f ∉ E := by
    intro hfin
    have hLne : L ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hLtwo
      omega
    obtain ⟨A, hA, hAne⟩ := L.ne_bot_iff.mp hLne
    have hex : ∃ v, A v ≠ 0 := by
      by_contra! hh
      exact hAne (LinearMap.ext hh)
    obtain ⟨v, hv⟩ := hex
    have hvE : A v ∈ E :=
      ((Submodule.span_singleton_le_iff_mem f E).mpr hfin) (hline A hA ⟨v, rfl⟩)
    have hvO : A v ∈ Eᗮ := by
      obtain ⟨Q, rfl⟩ := hA
      exact Eᗮ.starProjection_apply_mem ((Q : V →L[ℝ] V) v)
    have hzero : A v ∈ E ⊓ Eᗮ := ⟨hvE, hvO⟩
    rw [E.inf_orthogonal_eq_bot] at hzero
    exact hv hzero
  let U := E ⊔ (ℝ ∙ f)
  have hdis : Disjoint E (ℝ ∙ f) := Submodule.disjoint_span_singleton_of_notMem hfE
  have hU : finrank ℝ U = d := by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq E (ℝ ∙ f)
    rw [hdis.eq_bot, finrank_bot, add_zero, finrank_span_singleton hf] at hh
    rw [hUdim] at hEdim
    exact hh.trans hEdim
  have hle : P ≤ quadraticSpaceSupportedOperators U := by
    intro Q hQ
    refine ⟨hP Q hQ, fun v ↦ ?_⟩
    have hpE : E.starProjection (Q v) ∈ E := E.starProjection_apply_mem (Q v)
    have hpL : Eᗮ.starProjection (Q v) ∈ ℝ ∙ f :=
      hline (F ⟨Q, hQ⟩) ⟨⟨Q, hQ⟩, rfl⟩ ⟨v, rfl⟩
    have hEU : E ≤ U := le_sup_left
    have hfU : (ℝ ∙ f : Submodule ℝ V) ≤ U := le_sup_right
    have hs : E.starProjection (Q v) + Eᗮ.starProjection (Q v) ∈ U :=
      U.add_mem (hEU hpE) (hfU hpL)
    rwa [E.starProjection_add_starProjection_orthogonal (Q v)] at hs
  refine ⟨U, hU, Submodule.eq_of_le_of_finrank_le hle ?_⟩
  have hb := quadraticSpaceSupportedOperators_finrank_le U
  rw [hU] at hb
  rwa [heq]

#print axioms quadraticSpace_equality_classification
#print axioms quadraticSpace_projected_evaluation_dependent
#print axioms quadraticSpace_projected_evaluation_dependent_everywhere
#print axioms quadraticSpaceProjectionMap
#print axioms quadraticSpace_projected_space_finrank
#print axioms quadraticSpace_equality_kernel_supported
#print axioms quadraticSpace_projected_finrank_le_one
end GlobalEmbedding.Paper
