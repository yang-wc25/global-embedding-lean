import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# Local linear syzygies for the original supported-rank bound

Source: ROOT's target-preserving local argument in
`coord/reviews/revised-audit-root-syzygy-alternative.md`, replacing only the
good-evaluation consumer of original main.tex 1024–1029. DAG node:
`supported-rank-local-syzygy-span`. All maps below use native linear maps.
-/

noncomputable section

open Module Set
open scoped Topology

namespace GlobalEmbedding.Paper

variable {U K : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup K] [Module ℝ K]

local instance syzygyDualGroup : AddCommGroup (Module.Dual ℝ K) := LinearMap.addCommGroup
local instance syzygyDoubleDualGroup : AddCommGroup (Module.Dual ℝ (Module.Dual ℝ K)) :=
  LinearMap.addCommGroup
local instance syzygyBilinearGroup :
    AddCommGroup (U →ₗ[ℝ] Module.Dual ℝ (Module.Dual ℝ K)) := LinearMap.addCommGroup

/-- The literal quadratic evaluation functional on the given family. -/
def supportedRankQuadraticEvaluation (Q : K →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (z : U) : Module.Dual ℝ K where
  toFun k := Q k z z
  map_add' k l := by simp
  map_smul' c k := by simp

/-- The literal raw legal U-valued kernel column. -/
def supportedRankRawColumn (Q : K →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (z : U) : K →ₗ[ℝ] U :=
  (supportedRankQuadraticEvaluation Q z).smulRight z

/-- A dual Hom functional paired with actual rank-one maps, without trace conventions. -/
def supportedRankDualBilinear :
    Module.Dual ℝ (K →ₗ[ℝ] U) →ₗ[ℝ] U →ₗ[ℝ] Module.Dual ℝ (Module.Dual ℝ K) where
  toFun l := LinearMap.mk₂ ℝ (fun v a ↦ l (a.smulRight v))
    (by
      intro v w a
      rw [show a.smulRight (v + w) = a.smulRight v + a.smulRight w by ext; simp]
      simp)
    (by
      intro c v a
      rw [show a.smulRight (c • v) = c • a.smulRight v by ext; simp [smul_smul, mul_comm]]
      simp)
    (by
      intro v a b
      rw [show (a + b).smulRight v = a.smulRight v + b.smulRight v by ext; simp [add_smul]]
      simp)
    (by
      intro c v a
      rw [show (c • a).smulRight v = c • a.smulRight v by ext; simp [smul_smul]]
      simp)
  map_add' l m := by ext; simp
  map_smul' c l := by ext; simp

/-- Rank-one values determine the functional, by the native finite-basis expansion. -/
theorem supportedRankDualBilinear_injective [FiniteDimensional ℝ K] :
    Function.Injective (supportedRankDualBilinear (U := U) (K := K)) := by
  classical
  intro l m h
  let b := Module.finBasis ℝ K
  ext T
  have hT : T = ∑ i, (b.coord i).smulRight (T (b i)) := by
    ext k
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Basis.coord_apply]
    change T k = ∑ i, (b.repr k) i • T (b i)
    calc
      T k = T (∑ i, (b.repr k) i • b i) := congrArg T (b.sum_repr k).symm
      _ = _ := by simp only [map_sum, map_smul]
  rw [hT, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun B ↦ B (T (b i)) (b.coord i)) h

/-- A local scalar polynomial identity has zero linear and quadratic coefficients.
This uses the native polynomial identity theorem, not cubic monomial counting. -/
theorem supportedRank_local_coefficients
    (c0 c1 c2 c3 : ℝ)
    (h : ∀ᶠ t : ℝ in 𝓝 0, c0 + t * c1 + t ^ 2 * c2 + t ^ 3 * c3 = 0) :
    c1 = 0 ∧ c2 = 0 := by
  let p : Polynomial ℝ :=
    Polynomial.C c0 + Polynomial.X * Polynomial.C c1 +
      Polynomial.X ^ 2 * Polynomial.C c2 + Polynomial.X ^ 3 * Polynomial.C c3
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (infinite_of_mem_nhds 0 h).mono
    intro t ht
    change c0 + t * c1 + t ^ 2 * c2 + t ^ 3 * c3 = 0 at ht
    change p.eval t = 0
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    nlinarith [ht]
  constructor
  · have hc := congrArg (fun q : Polynomial ℝ ↦ q.coeff 1) hp
    simpa [p] using hc
  · have hc := congrArg (fun q : Polynomial ℝ ↦ q.coeff 2) hp
    simpa [p] using hc

/-- The middle coefficient is kept intact; callers may eliminate its Hessian contribution
only after proving the evaluation-kernel condition. -/
theorem supportedRank_local_quadratic_coefficient
    (c0 c1 c2 c3 : ℝ)
    (h : ∀ᶠ t : ℝ in 𝓝 0, c0 + t * c1 + t ^ 2 * c2 + t ^ 3 * c3 = 0) :
    c2 = 0 :=
  (supportedRank_local_coefficients c0 c1 c2 c3 h).2

/-- Exact quadratic expansion, with the same factor two as the genuine derivative. -/
theorem supportedRankQuadraticEvaluation_add_smul
    (Q : K →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (hQ : ∀ k v w, Q k v w = Q k w v)
    (z v : U) (t : ℝ) (J : U →ₗ[ℝ] Module.Dual ℝ K)
    (hJ : ∀ v k, J v k = 2 * Q k z v) :
    supportedRankQuadraticEvaluation Q (z + t • v) =
      supportedRankQuadraticEvaluation Q z + t • J v +
        t ^ 2 • supportedRankQuadraticEvaluation Q v := by
  ext k
  simp only [supportedRankQuadraticEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
    map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hJ]
  rw [hQ k v z]
  ring

section LocalIdentity

variable [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]

/-- The second-order local identity before imposing an evaluation-kernel condition.
The term B(z,D²a(v,v))/2 is explicitly present as B z (a v). -/
theorem supportedRank_local_hessian_identity
    (Q : K →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (hQ : ∀ k v w, Q k v w = Q k w v)
    (Ω : Set U) (hΩ : IsOpen Ω) (z : U) (hz : z ∈ Ω)
    (J : U →ₗ[ℝ] Module.Dual ℝ K) (hJ : ∀ v k, J v k = 2 * Q k z v)
    (B : U →ₗ[ℝ] Module.Dual ℝ (Module.Dual ℝ K))
    (hB : ∀ x ∈ Ω, B x (supportedRankQuadraticEvaluation Q x) = 0) (v : U) :
    B v (J v) + B z (supportedRankQuadraticEvaluation Q v) = 0 := by
  have ht : ∀ᶠ t : ℝ in 𝓝 0, z + t • v ∈ Ω := by
    exact (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      |>.eventually (by simpa using hΩ.mem_nhds hz)
  apply supportedRank_local_quadratic_coefficient
    (B z (supportedRankQuadraticEvaluation Q z))
    (B v (supportedRankQuadraticEvaluation Q z) + B z (J v))
    _ (B v (supportedRankQuadraticEvaluation Q v))
  filter_upwards [ht] with t ht
  have he := hB (z + t • v) ht
  rw [supportedRankQuadraticEvaluation_add_smul Q hQ z v t J hJ] at he
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul] at he
  nlinarith [he]

end LocalIdentity

/-- An alternating family of bilinear forms, in the native `Fin 2` exterior-power API. -/
def supportedRankAlternatingFamily
    {S H : Type*} [AddCommMonoid S] [Module ℝ S] [AddCommMonoid H] [Module ℝ H]
    (F : S →ₗ[ℝ] H →ₗ[ℝ] Module.Dual ℝ H) (hF : ∀ s v, F s v v = 0) :
    S →ₗ[ℝ] H [⋀^Fin 2]→ₗ[ℝ] ℝ where
  toFun s :=
    { toFun := fun v ↦ F s (v 0) (v 1)
      map_update_add' := by
        intro _ v i x y
        fin_cases i <;> simp
      map_update_smul' := by
        intro _ v i c x
        fin_cases i <;> simp
      map_eq_zero_of_eq' := by
        intro v i j hij hne
        fin_cases i <;> fin_cases j <;> simp_all }
  map_add' s t := by ext v; simp
  map_smul' c s := by ext v; simp

/-- Native exterior-power dimension for alternating bilinear forms. -/
theorem supportedRank_alternating_finrank
    {H : Type*} [AddCommGroup H] [Module ℝ H] [FiniteDimensional ℝ H] :
    finrank ℝ (H [⋀^Fin 2]→ₗ[ℝ] ℝ) = (finrank ℝ H).choose 2 := by
  rw [(exteriorPower.alternatingMapLinearEquiv (R := ℝ) (M := H) (N := ℝ)
    (n := 2)).finrank_eq]
  simp

section SpanBound

/-- The actual local raw-column span, not a formal-label or polynomial coefficient space. -/
def supportedRankLocalRawSpan (Q : K →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (Ω : Set U) :
    Submodule ℝ (K →ₗ[ℝ] U) :=
  Submodule.span ℝ (supportedRankRawColumn Q '' Ω)

/-- A true span-annihilator functional satisfies the local syzygy identity. -/
theorem supportedRank_annihilator_identity
    (Q : K →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (Ω : Set U)
    (l : (supportedRankLocalRawSpan Q Ω).dualAnnihilator) (z : U) (hz : z ∈ Ω) :
    supportedRankDualBilinear l.val z (supportedRankQuadraticEvaluation Q z) = 0 := by
  exact (Submodule.mem_dualAnnihilator _).mp l.property _
    (Submodule.subset_span ⟨z, hz, rfl⟩)

variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ K]
variable [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]

/-- The syzygy-space dimension bound, with the actual good derivative evaluation.
Its proof restricts radical forms to the native kernel of a functional taking z0 to one;
this is a concrete complement of the line, avoiding any additional quotient-form carrier. -/
theorem supportedRank_syzygy_finrank_bound
    (Q : K →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (hQ : ∀ k v w, Q k v w = Q k w v)
    (Ω : Set U) (hΩ : IsOpen Ω) (z : U) (hz : z ∈ Ω) (hz0 : z ≠ 0)
    (J : U ≃ₗ[ℝ] Module.Dual ℝ K) (hJ : ∀ v k, J v k = 2 * Q k z v)
    (S : Submodule ℝ (U →ₗ[ℝ] Module.Dual ℝ (Module.Dual ℝ K)))
    (hS : ∀ B ∈ S, ∀ x ∈ Ω, B x (supportedRankQuadraticEvaluation Q x) = 0) :
    finrank ℝ S ≤ (finrank ℝ U).choose 2 := by
  classical
  let a := supportedRankQuadraticEvaluation Q z
  have ha : a ≠ 0 := by
    intro ha
    apply hz0
    apply J.injective
    ext k
    have hk : Q k z z = 0 := congrArg (fun f : Module.Dual ℝ K ↦ f k) ha
    simp [hJ, hk]
  let E : S →ₗ[ℝ] Module.Dual ℝ (Module.Dual ℝ K) :=
    { toFun := fun B ↦ B.val z
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let e : Module.Dual ℝ (Module.Dual ℝ (Module.Dual ℝ K)) :=
    Module.Dual.eval ℝ (Module.Dual ℝ K) a
  have he : e ≠ 0 := by
    intro he
    apply ha
    exact (Module.eval_apply_injective ℝ) (by simpa [e] using he)
  have hEr : LinearMap.range E ≤ LinearMap.ker e := by
    rintro _ ⟨B, rfl⟩
    exact hS B.val B.property z hz
  have hd : finrank ℝ K = finrank ℝ U := by
    simpa using J.finrank_eq.symm
  have hErank : finrank ℝ (LinearMap.range E) + 1 ≤ finrank ℝ U := by
    have := Submodule.finrank_mono hEr
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero he
    simp only [Subspace.dual_finrank_eq] at hh
    omega
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℝ hz0
  let H := LinearMap.ker f
  have hf0 : f ≠ 0 := by intro h; simp [h] at hf
  have hH : finrank ℝ H + 1 = finrank ℝ U :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hf0
  have hEzero (B : LinearMap.ker E) : B.val.val z = 0 := B.property
  have hdiag (B : LinearMap.ker E) (v : U) : B.val.val v (J v) = 0 := by
    have hi := supportedRank_local_hessian_identity Q hQ Ω hΩ z hz J.toLinearMap hJ
      B.val.val (hS B.val.val B.val.property) v
    simpa [hEzero B] using hi
  have hswap (B : LinearMap.ker E) (v w : U) :
      B.val.val v (J w) + B.val.val w (J v) = 0 := by
    have hh := hdiag B (v + w)
    simp only [map_add, LinearMap.add_apply] at hh
    linarith [hdiag B v, hdiag B w]
  have hzright (B : LinearMap.ker E) (v : U) : B.val.val v (J z) = 0 := by
    simpa [hEzero B] using hswap B v z
  let F : LinearMap.ker E →ₗ[ℝ] H →ₗ[ℝ] Module.Dual ℝ H :=
    { toFun := fun B ↦ ((B.val.val.compl₂ J.toLinearMap).comp H.subtype).compl₂ H.subtype
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  let A := supportedRankAlternatingFamily (S := LinearMap.ker E) (H := H) F
    (fun B v ↦ hdiag B v.val)
  have hAi : Function.Injective A := by
    intro B C hBC
    apply Subtype.ext
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro μ
    obtain ⟨w, rfl⟩ := J.surjective μ
    let vH : H := ⟨v - f v • z, by simp [H, hf]⟩
    let wH : H := ⟨w - f w • z, by simp [H, hf]⟩
    have hres := congrArg (fun T ↦ T ![vH, wH]) hBC
    change B.val.val (v - f v • z) (J (w - f w • z)) =
      C.val.val (v - f v • z) (J (w - f w • z)) at hres
    simpa only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      hEzero B, hEzero C, LinearMap.zero_apply, hzright B, hzright C,
      smul_eq_mul, mul_zero, sub_zero, zero_sub, map_neg, neg_zero] using hres
  let ext := exteriorPower.alternatingMapLinearEquiv (R := ℝ) (M := H) (N := ℝ) (n := 2)
  have hk := LinearMap.finrank_le_finrank_of_injective
    (f := ext.toLinearMap.comp A) (ext.injective.comp hAi)
  simp only [Module.finrank_linearMap_self, exteriorPower.finrank_eq] at hk
  have hsum := LinearMap.finrank_range_add_finrank_ker (K := ℝ) (V := S)
    (V₂ := Module.Dual ℝ (Module.Dual ℝ K)) E
  have hc : (finrank ℝ H + 1).choose 2 =
      (finrank ℝ H).choose 2 + finrank ℝ H := by
    simpa [Nat.choose_one_right, Nat.add_comm] using (Nat.choose_succ_succ (finrank ℝ H) 1)
  rw [← hH, hc]
  omega

/-- The two triangular dimensions add to the dimension of the full square Hom space. -/
theorem supportedRank_triangular_dimension (d : ℕ) :
    d.choose 2 + (d + 1).choose 2 = d * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := Nat.choose_succ_succ d 1
    have h2 := Nat.choose_succ_succ (d + 1) 1
    simp only [Nat.choose_one_right] at h1 h2
    nlinarith

/-- ROOT's local linear-syzygy bound for the SAME literal raw legal columns.
The only nondegeneracy assumption is the actual good derivative-evaluation isomorphism.
No desired span dimension, alternating form, or normal-rank conclusion is assumed. -/
theorem supportedRank_local_raw_span_finrank
    (Q : K →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (hQ : ∀ k v w, Q k v w = Q k w v)
    (Ω : Set U) (hΩ : IsOpen Ω) (z : U) (hz : z ∈ Ω) (hz0 : z ≠ 0)
    (J : U ≃ₗ[ℝ] Module.Dual ℝ K) (hJ : ∀ v k, J v k = 2 * Q k z v) :
    finrank ℝ U * (finrank ℝ U + 1) / 2 ≤ finrank ℝ (supportedRankLocalRawSpan Q Ω) := by
  let L := supportedRankLocalRawSpan Q Ω
  let S := L.dualAnnihilator.map (supportedRankDualBilinear (U := U) (K := K))
  have hi := supportedRankDualBilinear_injective (U := U) (K := K)
  have hdimS : finrank ℝ L.dualAnnihilator = finrank ℝ S :=
    (Submodule.equivMapOfInjective supportedRankDualBilinear hi L.dualAnnihilator).finrank_eq
  have hS : ∀ B ∈ S, ∀ x ∈ Ω,
      B x (supportedRankQuadraticEvaluation Q x) = 0 := by
    rintro _ ⟨l, hl, rfl⟩ x hx
    exact supportedRank_annihilator_identity Q Ω ⟨l, hl⟩ x hx
  have hbound := supportedRank_syzygy_finrank_bound Q hQ Ω hΩ z hz hz0 J hJ S hS
  have hdim := Subspace.finrank_add_finrank_dualAnnihilator_eq L
  have hd : finrank ℝ K = finrank ℝ U := by simpa using J.finrank_eq.symm
  rw [Module.finrank_linearMap, hd, hdimS] at hdim
  have htri := supportedRank_triangular_dimension (finrank ℝ U)
  have hchoose : finrank ℝ U * (finrank ℝ U + 1) / 2 =
      (finrank ℝ U + 1).choose 2 := by simp [Nat.choose_two_right, Nat.mul_comm]
  change finrank ℝ U * (finrank ℝ U + 1) / 2 ≤ finrank ℝ L
  rw [hchoose]
  omega

omit [FiniteDimensional ℝ U] in
/-- The SAME local quadratic evaluations span the full dual of K. This supplies the
independent t-difference directions, before any compression or moving-support quotient. -/
theorem supportedRank_local_evaluation_span
    (Q : K →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (hQ : ∀ k v w, Q k v w = Q k w v)
    (Ω : Set U) (hΩ : IsOpen Ω) (z : U) (hz : z ∈ Ω)
    (J : U ≃ₗ[ℝ] Module.Dual ℝ K) (hJ : ∀ v k, J v k = 2 * Q k z v) :
    Submodule.span ℝ (supportedRankQuadraticEvaluation Q '' Ω) = ⊤ := by
  let L := Submodule.span ℝ (supportedRankQuadraticEvaluation Q '' Ω)
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro l hl
  change l = 0
  ext μ
  obtain ⟨v, rfl⟩ := J.surjective μ
  have ht : ∀ᶠ t : ℝ in 𝓝 0, z + t • v ∈ Ω := by
    exact (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      |>.eventually (by simpa using hΩ.mem_nhds hz)
  have hh : ∀ᶠ t : ℝ in 𝓝 0,
      l (supportedRankQuadraticEvaluation Q z) + t * l (J v) +
        t ^ 2 * l (supportedRankQuadraticEvaluation Q v) + t ^ 3 * 0 = 0 := by
    filter_upwards [ht] with t ht
    have he := (Submodule.mem_dualAnnihilator _).mp hl _
      (Submodule.subset_span ⟨z + t • v, ht, rfl⟩)
    rw [supportedRankQuadraticEvaluation_add_smul Q hQ z v t J.toLinearMap hJ] at he
    simpa only [map_add, map_smul, smul_eq_mul, mul_zero, add_zero,
      LinearEquiv.coe_coe] using he
  exact (supportedRank_local_coefficients _ _ _ _ hh).1

end SpanBound

end GlobalEmbedding.Paper
