import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Isomorphisms

/-! Actual pointwise-dependent map algebra used in the equality case of revised
quadratic-space lemma, lines1828–1839. Reuses native homothety theorem on range A. -/

noncomputable section
namespace GlobalEmbedding.Paper

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Over the reals, dependence on a nonzero vector means actual membership in its line. -/
theorem quadraticSpace_mem_span_of_dependent {u v : W} (hu : u ≠ 0)
    (h : ¬ LinearIndependent ℝ ![u, v]) : v ∈ ℝ ∙ u := by
  rw [Submodule.mem_span_singleton]
  by_contra! hn
  exact h ((LinearIndependent.pair_iff' hu).mpr hn)

/-- Pointwise dependence forces ker A into ker B as soon as A has two independent
values. This includes points where A vanishes: dependence there alone says nothing,
so x+z and y+z are essential.
Source: revised lemma proof1834–1836. -/
theorem quadraticSpace_ker_le_of_pointwise_dependent
    (A B : V →ₗ[ℝ] W) {x y : V}
    (hxy : LinearIndependent ℝ ![A x, A y])
    (hdep : ∀ v, ¬ LinearIndependent ℝ ![A v, B v]) : A.ker ≤ B.ker := by
  have hx : A x ≠ 0 := by simpa using hxy.ne_zero 0
  have hy : A y ≠ 0 := by simpa using hxy.ne_zero 1
  intro z hz
  have hz' : A z = 0 := hz
  have hspan (v : V) (hv : A v ≠ 0) : B z ∈ ℝ ∙ A v := by
    have h₁ := quadraticSpace_mem_span_of_dependent hv (hdep v)
    have h₂ : B (v + z) ∈ ℝ ∙ A v := by
      simpa [map_add, hz'] using
        quadraticSpace_mem_span_of_dependent (by simpa [map_add, hz'] using hv) (hdep (v + z))
    have hh := (ℝ ∙ A v : Submodule ℝ W).sub_mem h₂ h₁
    simpa [map_add] using hh
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan x hx)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hspan y hy)
  have hab := hxy.eq_zero_of_pair' (ha.trans hb.symm)
  change B z = 0
  simpa [hab.1] using ha.symm

/-- A pointwise-dependent companion of a map with two independent image vectors
is one scalar multiple globally. Native range factorization and Mathlib's existing
homothety lemma supply the scalar; no new classification is postulated.
Source: revised1828–1836. -/
theorem quadraticSpace_eq_smul_of_pointwise_dependent
    (A B : V →ₗ[ℝ] W) {x y : V}
    (hxy : LinearIndependent ℝ ![A x, A y])
    (hdep : ∀ v, ¬ LinearIndependent ℝ ![A v, B v]) : ∃ c : ℝ, B = c • A := by
  classical
  have hker := quadraticSpace_ker_le_of_pointwise_dependent A B hxy hdep
  have hpoint (v : V) : B v ∈ ℝ ∙ A v := by
    by_cases hv : A v = 0
    · have hB : B v = 0 := hker hv
      simp [hB]
    · exact quadraticSpace_mem_span_of_dependent hv (hdep v)
  have hsurj : Function.Surjective A.rangeRestrict :=
    LinearMap.range_eq_top.mp A.range_rangeRestrict
  have hkerR : A.rangeRestrict.ker ≤ B.ker := by simpa using hker
  let f₀ : A.range →ₗ[ℝ] W :=
    A.rangeRestrict.liftOfSurjective hsurj ⟨B, hkerR⟩
  have hfac (v : V) : f₀ (A.rangeRestrict v) = B v :=
    LinearMap.equivOfSurjective_apply _ _
  have hfr (u : A.range) : f₀ u ∈ A.range := by
    obtain ⟨v, hv⟩ := hsurj u
    rw [← hv, hfac]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hpoint v)
    rw [← hc]
    exact A.range.smul_mem c ⟨v, rfl⟩
  let f : A.range →ₗ[ℝ] A.range := f₀.codRestrict A.range hfr
  have hline (u : A.range) : ∃ c : ℝ, c • u = f u := by
    obtain ⟨v, hv⟩ := hsurj u
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hpoint v)
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa [← hv, f, hfac] using hc
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (f := f)
    (fun u hli ↦ by
      obtain ⟨a, ha⟩ := hline u
      have hu : u ≠ 0 := by simpa using hli.ne_zero 0
      exact (LinearIndependent.pair_iff' hu).mp hli a ha)
  refine ⟨c, ?_⟩
  ext v
  have hh := congrArg (fun g : A.range →ₗ[ℝ] A.range ↦ (g (A.rangeRestrict v) : W)) hc
  simpa [f, hfac] using hh

#print axioms quadraticSpace_ker_le_of_pointwise_dependent
#print axioms quadraticSpace_eq_smul_of_pointwise_dependent

end GlobalEmbedding.Paper
