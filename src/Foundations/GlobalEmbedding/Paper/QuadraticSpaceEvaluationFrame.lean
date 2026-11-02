import GlobalEmbedding.Paper.QuadraticSpaceKernelSupport
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! Actual maximum-rank columns and actual smooth Gram coefficient reconstruction.
Source: revised manuscript1791–1809; no local frame or coefficients are final inputs. -/

noncomputable section
open scoped Topology Manifold ContDiff
open Module

namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The maximum actual evaluation rank is attained, including a zero ambient space. -/
theorem quadraticSpace_exists_maximal_evaluation
    (P : Submodule ℝ (V →L[ℝ] V)) :
    ∃ x₀ : V, ∀ x : V,
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤
        finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap) := by
  let f (x : V) := finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap)
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨finrank ℝ V, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Submodule.finrank_le _
  obtain ⟨_, ⟨x₀, rfl⟩, hmax⟩ :=
    hbdd.exists_isGreatest_of_nonempty (Set.range_nonempty f)
  exact ⟨x₀, fun x ↦ hmax ⟨x, rfl⟩⟩

/-- A genuine linear right inverse of the base evaluation constructs columns with
A(x0)=inclusion of U0=P x0. Nearby these columns span the ENTIRE evaluation image,
by maximum rank, not just some selected subspace.
Source: revised1798–1805. -/
theorem quadraticSpace_maximal_evaluation_frame
    (P : Submodule ℝ (V →L[ℝ] V)) (x₀ : V)
    (hmax : ∀ x : V,
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤
        finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap)) :
    ∃ A : V →L[ℝ] (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap) →L[ℝ] V,
      A x₀ = (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap).subtypeL ∧
      ∀ᶠ x in 𝓝 x₀, Function.Injective (A x) ∧
        LinearMap.range (A x).toLinearMap =
          LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap := by
  let T := (quadraticSpaceEvaluation P x₀).toLinearMap
  let U := T.range
  obtain ⟨r, hr⟩ := T.rangeRestrict.exists_rightInverse_of_surjective T.range_rangeRestrict
  let F : U →L[ℝ] (V →L[ℝ] V) := P.subtypeL.comp r.toContinuousLinearMap
  let A : V →L[ℝ] U →L[ℝ] V := F.flip
  have hbase : A x₀ = U.subtypeL := by
    ext u
    exact congrArg Subtype.val (LinearMap.congr_fun hr u)
  have hi₀ : Function.Injective (A x₀) := by
    rw [hbase]
    exact Subtype.val_injective
  have hi : ∀ᶠ x in 𝓝 x₀, Function.Injective (A x) :=
    (ContinuousLinearMap.isOpen_injective.preimage A.continuous).mem_nhds hi₀
  refine ⟨A, hbase, ?_⟩
  filter_upwards [hi] with x hx
  refine ⟨hx, ?_⟩
  have hle : LinearMap.range (A x).toLinearMap ≤
      LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap := by
    rintro _ ⟨u, rfl⟩
    exact ⟨r u, rfl⟩
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [LinearMap.finrank_range_of_inj hx]
  exact hmax x

/-- The actual Gram coefficient field supplies the kernel-range conclusion at
any maximal-rank point. No differentiability, frame or solver is assumed here:
all are constructed from the operator space and maximum evaluation rank.
Source: revised1800–1809. -/
theorem quadraticSpace_maximal_kernel_range
    (P : Submodule ℝ (V →L[ℝ] V)) (x₀ : V)
    (hmax : ∀ x : V,
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤
        finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap))
    (Q : V →L[ℝ] V) (hQ : Q ∈ P) (hzero : Q x₀ = 0) :
    LinearMap.range Q.toLinearMap ≤
      LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap := by
  obtain ⟨A, hbase, hlocal⟩ := quadraticSpace_maximal_evaluation_frame P x₀ hmax
  let U := LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap
  let s := {x : V | Function.Injective (A x)}
  have hs : IsOpen s := ContinuousLinearMap.isOpen_injective.preimage A.continuous
  have hx₀ : x₀ ∈ s := by
    change Function.Injective (A x₀)
    rw [hbase]
    exact Subtype.val_injective
  let C (x : V) : V →L[ℝ] U := ((A x).adjoint.comp (A x)).inverse.comp (A x).adjoint
  have hA0 : ContDiff ℝ 1 A := by fun_prop
  have hA : ContDiffOn ℝ 1 (fun x ↦ A x) s := hA0.contDiffOn
  have hAm : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, U →L[ℝ] V) 1 (fun x ↦ A x) s :=
    hA.contMDiffOn
  have hC : ContDiffOn ℝ 1 C s :=
    (smooth_frame_gram_coefficients (n := 1) (s := s) (fun x ↦ A x) hAm
      (fun _ hx ↦ hx)).contDiffOn
  have hCd : DifferentiableAt ℝ C x₀ :=
    (hC.contDiffAt (hs.mem_nhds hx₀)).differentiableAt_one
  let c (x : V) := C x (Q x)
  have hc : DifferentiableAt ℝ c x₀ := hCd.clm_apply Q.differentiableAt
  have hc₀ : c x₀ = 0 := by simp [c, hzero]
  have heq : (fun x ↦ A x (c x)) =ᶠ[𝓝 x₀] Q := by
    filter_upwards [hlocal] with x hx
    have hmem : Q x ∈ LinearMap.range (A x).toLinearMap := by
      rw [hx.2]
      exact ⟨⟨Q, hQ⟩, rfl⟩
    have hh := congrArg (fun T : V →L[ℝ] V ↦ T (Q x))
      (frame_gram_inverse_identities (A x) hx.1).2
    exact hh.trans (Submodule.starProjection_eq_self_iff.mpr hmem)
  have hr := quadraticSpace_kernel_range_of_local_coefficients A c Q x₀ A
    (fderiv ℝ c x₀) A.hasFDerivAt hc.hasFDerivAt hc₀ heq
  simpa [hbase] using hr

omit [FiniteDimensional ℝ V] in
/-- A real selfadjoint quadratic cannot vanish on a nonempty open set unless
its actual operator is zero. The native derivative is twice the actual inner
functional; a second local derivative then identifies the zero operator.
Source: revised1792–1795, with omitted polarization fully expanded. -/
theorem quadraticSpace_eq_zero_of_quadratic_zero_on_open
    (Q : V →L[ℝ] V) (hQ : Q.toLinearMap.IsSymmetric)
    {s : Set V} (hs : IsOpen s) (hne : s.Nonempty)
    (hzero : ∀ x ∈ s, inner ℝ (Q x) x = 0) : Q = 0 := by
  have hQzero (x : V) (hx : x ∈ s) : Q x = 0 := by
    have heq : Q.reApplyInnerSelf =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hzero y hy
    have hd := (hQ.hasStrictFDerivAt_reApplyInnerSelf x).hasFDerivAt.congr_of_eventuallyEq heq.symm
    have hh : 2 • innerSL ℝ (Q x) = 0 := hd.unique (hasFDerivAt_const (0 : ℝ) x)
    have hv := congrArg (fun L : V →L[ℝ] ℝ ↦ L (Q x)) hh
    have hv' : 2 * inner ℝ (Q x) (Q x) = 0 := by simpa using hv
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    linarith
  obtain ⟨x, hx⟩ := hne
  have heq : Q =ᶠ[𝓝 x] (fun _ ↦ (0 : V)) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hQzero y hy
  exact (Q.hasFDerivAt.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_const (0 : V) x)

/-- A nonzero selfadjoint operator space has a maximum-rank evaluation point
which is not perpendicular to its evaluation image. Both conditions are derived,
not added as a hypothesis of the final dimension theorem.
Source: revised1791–1797. -/
theorem quadraticSpace_exists_maximal_nonorthogonal
    (P : Submodule ℝ (V →L[ℝ] V))
    (hP : ∀ Q ∈ P, Q.toLinearMap.IsSymmetric) (hne : P ≠ ⊥) :
    ∃ x₀ : V, (∀ x : V,
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤
        finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap)) ∧
      ∃ Q ∈ P, inner ℝ (Q x₀) x₀ ≠ 0 := by
  obtain ⟨Q, hQ, hQne⟩ := P.ne_bot_iff.mp hne
  obtain ⟨x, hmax⟩ := quadraticSpace_exists_maximal_evaluation P
  obtain ⟨A, _, hlocal⟩ := quadraticSpace_maximal_evaluation_frame P x hmax
  have hrank : ∀ᶠ y in 𝓝 x,
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P y).toLinearMap) =
        finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) := by
    filter_upwards [hlocal] with y hy
    rw [← hy.2, LinearMap.finrank_range_of_inj hy.1]
  obtain ⟨s, hsub, hs, hxs⟩ := mem_nhds_iff.mp hrank
  have hnzero : ∃ y ∈ s, inner ℝ (Q y) y ≠ 0 := by
    by_contra! hn
    exact hQne (quadraticSpace_eq_zero_of_quadratic_zero_on_open Q (hP Q hQ)
      hs ⟨x, hxs⟩ hn)
  obtain ⟨y, hy, hquad⟩ := hnzero
  refine ⟨y, ?_, Q, hQ, hquad⟩
  intro z
  rw [hsub hy]
  exact hmax z

#print axioms quadraticSpace_eq_zero_of_quadratic_zero_on_open
#print axioms quadraticSpace_exists_maximal_nonorthogonal
#print axioms quadraticSpace_exists_maximal_evaluation
#print axioms quadraticSpace_maximal_evaluation_frame
#print axioms quadraticSpace_maximal_kernel_range

end GlobalEmbedding.Paper
