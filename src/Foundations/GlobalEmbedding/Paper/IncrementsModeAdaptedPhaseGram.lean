import GlobalEmbedding.Paper.IncrementsModeCoefficientRegularity
import GlobalEmbedding.Paper.IncrementsSymmetricCoordinateProducts
import GlobalEmbedding.Paper.GoodCovector
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# The original adapted good phase gives the SAME transverse Gram inverse

Source: `main.tex`, lem:increments, (6.2), lines 617–643.
DAG: `increments-mode-adapted-phase-beta-gram`. Exclusive worker W2.
Only actual original phase/coordinate geometry is used; uniform bounds remain open.
-/

noncomputable section
open Manifold Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Paper

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "D0" => EuclideanSpace ℝ (Fin m)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "P" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ P

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]

/-- Good of the actual transported first coordinate makes the ORIGINAL beta Gram
invertible. The inverse-chart differential sends the native zero-first coordinates
into its kernel. Map the accepted once-sorted product independence, then use the
injective true-B restriction in algebraic Good. Native frame Gram positivity and
the exact accepted ambient-frame Gram identity finish. No Gram/margin or auxiliary
Riemannian metric is assumed. Source: transverse beta in original (6.2). -/
theorem incrementsModeTransverseGram_of_goodChart (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (y : M) (x : D)
    (hx : x ∈ (extChartAt 𝓙 y).target)
    (hgood : GoodCovector F hF ((extChartAt 𝓙 y).symm x)
      ((EuclideanSpace.proj 0).comp
        (mfderiv 𝓙 𝓙 (extChartAt 𝓙 y) ((extChartAt 𝓙 y).symm x)))) :
    let β := incrementsTransversePairing F hF ((extChartAt 𝓙 y).symm x)
      (fun a : Fin m ↦ incrementsModeCoordinateDirections (extChartAt 𝓙 y).symm x a.succ)
    (β.comp β.adjoint).IsInvertible := by
  classical
  let c : D → M := (extChartAt 𝓙 y).symm
  let A : D →L[ℝ] TangentSpace 𝓙 (c x) := mfderiv 𝓙 𝓙 c x
  let H : TangentSpace 𝓙 (c x) →L[ℝ] D := mfderiv 𝓙 𝓙 (extChartAt 𝓙 y) (c x)
  let ξ := (EuclideanSpace.proj 0).comp H
  have hHA : H.comp A = ContinuousLinearMap.id ℝ D := by
    have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓙) hx
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at h
    exact h
  let ins : D0 →ₗ[ℝ] D :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toLinearMap.comp
      ((0 : D0 →ₗ[ℝ] ℝ).vecCons (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap)
  have hins (v : D0) : ins v 0 = 0 := rfl
  have hinss (v : D0) (a : Fin m) : ins v a.succ = v a := rfl
  let e : D0 →ₗ[ℝ] ξ.ker :=
    (A.toLinearMap.comp ins).codRestrict ξ.ker (by
      intro v
      change (H (A (ins v))) 0 = 0
      rw [← ContinuousLinearMap.comp_apply, hHA]
      exact hins v)
  have hei : Function.Injective e := by
    intro u v huv
    have h := congrArg (fun w : ξ.ker ↦ H w.val) huv
    change H (A (ins u)) = H (A (ins v)) at h
    change (H.comp A) (ins u) = (H.comp A) (ins v) at h
    rw [hHA] at h
    ext a
    exact congrArg (fun w : D ↦ w a.succ) h
  obtain ⟨p, hp⟩ := e.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hei)
  have hpe (v : D0) : p (e v) = v :=
    congrArg (fun L : D0 →ₗ[ℝ] D0 ↦ L v) hp
  have hli : LinearIndependent ℝ (fun q : P ↦
      symmetricSquareProduct ξ.ker (e (EuclideanSpace.single q.val.1 1))
        (e (EuclideanSpace.single q.val.2 1))) := by
    apply LinearIndependent.of_comp (symmetricSquareLinearMap p)
    change LinearIndependent ℝ (fun q : P ↦ symmetricSquareProduct D0
      (p (e (EuclideanSpace.single q.val.1 1))) (p (e (EuclideanSpace.single q.val.2 1))))
    simpa only [hpe] using
      increments_symmetric_coordinate_products_linearIndependent m
  have hg : Function.Injective
      ((trueSecondForm F hF (c x)).comp (symmetricSquareLinearMap ξ.ker.subtype)) :=
    hgood.2
  have hB := hli.map' _ (LinearMap.ker_eq_bot.mpr hg)
  have he_single (a : Fin m) :
      (e (EuclideanSpace.single a 1)).val =
        incrementsModeCoordinateDirections c x a.succ := by
    change A (ins (EuclideanSpace.single a 1)) = A (EuclideanSpace.single a.succ 1)
    congr 1
    ext b
    refine Fin.cases ?_ (fun j ↦ ?_) b
    · simp [hins]
    · simp [hinss, PiLp.single_apply]
  have hcols : LinearIndependent ℝ (fun q : P ↦
      incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ) := by
    convert hB using 1
    funext q
    symm
    change trueSecondForm F hF (c x)
      (symmetricSquareLinearMap ξ.ker.subtype
        (symmetricSquareProduct ξ.ker (e (EuclideanSpace.single q.val.1 1))
          (e (EuclideanSpace.single q.val.2 1)))) = _
    change trueSecondForm F hF (c x)
      (symmetricSquareProduct (TangentSpace 𝓙 (c x))
        (e (EuclideanSpace.single q.val.1 1)).val
        (e (EuclideanSpace.single q.val.2 1)).val) = _
    rw [he_single, he_single]
    rfl
  have hambi : Function.Injective (incrementsModeAmbientTransverseFrame F hF c x) := by
    intro u v huv
    have hs : (∑ q : P, (u q - v q) •
        incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
      change (∑ q : P, (u q - v q) •
        (incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ : V)) = 0
      have h := sub_eq_zero.mpr huv
      simpa [incrementsModeAmbientTransverseFrame, sub_smul, Finset.sum_sub_distrib] using h
    ext q
    exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hcols) _ hs q)
  have hi := (frame_gram_positive_invertible
    (incrementsModeAmbientTransverseFrame F hF c x) hambi).2.2
  rwa [incrementsModeAmbientTransverseFrame_gram] at hi

omit [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M] in
/-- The ORIGINAL adapted phase has exactly the transported first coordinate
covector. Differentiate the actual equality psi(c z)=z_0 on its original open
domain, use the native chain rule, and cancel the actual inverse-chart derivative.
This proves the covector identification instead of assuming it. Source: the
adapted coordinates x^1=psi immediately before original (6.2). -/
theorem incrementsModePhaseCovector_eq_chart (ψ : M → ℝ) (y : M) (Ω : Set D)
    (hΩ : IsOpen Ω) (hΩt : Ω ⊆ (extChartAt 𝓙 y).target) (x : D) (hx : x ∈ Ω)
    (hψ : MDifferentiableAt 𝓙 𝓘(ℝ, ℝ) ψ ((extChartAt 𝓙 y).symm x))
    (hadapt : ∀ z ∈ Ω, ψ ((extChartAt 𝓙 y).symm z) = z 0) :
    (tangentSpaceCastModel 𝓘(ℝ, ℝ) (ψ ((extChartAt 𝓙 y).symm x))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ, ℝ) ψ ((extChartAt 𝓙 y).symm x)) =
      (EuclideanSpace.proj 0).comp
        (mfderiv 𝓙 𝓙 (extChartAt 𝓙 y) ((extChartAt 𝓙 y).symm x)) := by
  let c : D → M := (extChartAt 𝓙 y).symm
  let A : D →L[ℝ] TangentSpace 𝓙 (c x) := mfderiv 𝓙 𝓙 c x
  let H : TangentSpace 𝓙 (c x) →L[ℝ] D := mfderiv 𝓙 𝓙 (extChartAt 𝓙 y) (c x)
  let d : TangentSpace 𝓙 (c x) →L[ℝ] ℝ :=
    (tangentSpaceCastModel 𝓘(ℝ, ℝ) (ψ (c x))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ, ℝ) ψ (c x))
  have hc : MDifferentiableAt 𝓙 𝓙 c x := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓙) (hΩt hx)
    simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using h
  have heq : ψ ∘ c =ᶠ[𝓝 x] (fun z : D ↦ z 0) :=
    Filter.eventuallyEq_of_mem (hΩ.mem_nhds hx) hadapt
  have hp : fderiv ℝ (ψ ∘ c) x = EuclideanSpace.proj 0 :=
    heq.fderiv_eq.trans (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (m + 1)) 0).fderiv
  have hm := mfderiv_comp x hψ hc
  rw [mfderiv_eq_fderiv, hp] at hm
  have hchain : d.comp A = EuclideanSpace.proj 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun L ↦
      (tangentSpaceCastModel 𝓘(ℝ, ℝ) (ψ (c x)))
        (L ((tangentSpaceCastModel 𝓙 x).symm v))) hm
    change (EuclideanSpace.proj 0) v = d (A v) at h
    exact h.symm
  have hAH : A.comp H = ContinuousLinearMap.id ℝ (TangentSpace 𝓙 (c x)) := by
    have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓙) (hΩt hx)
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at h
    exact h
  change d = (EuclideanSpace.proj 0).comp H
  calc
    d = d.comp (A.comp H) := by rw [hAH, ContinuousLinearMap.comp_id]
    _ = (d.comp A).comp H := rfl
    _ = _ := by rw [hchain]

/-- ORIGINAL Good of the actual source phase differential supplies the SAME
transverse beta-Gram inverse at every actual adapted chart point. Only the phase
derivative and actual adaptation are inputs, never the desired Gram conclusion.
Source: existence of the transverse J in original (6.2). -/
theorem incrementsModeTransverseGram_of_goodPhase (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (ψ : M → ℝ) (y : M) (Ω : Set D)
    (hΩ : IsOpen Ω) (hΩt : Ω ⊆ (extChartAt 𝓙 y).target) (x : D) (hx : x ∈ Ω)
    (hψ : MDifferentiableAt 𝓙 𝓘(ℝ, ℝ) ψ ((extChartAt 𝓙 y).symm x))
    (hadapt : ∀ z ∈ Ω, ψ ((extChartAt 𝓙 y).symm z) = z 0)
    (hgood : GoodCovector F hF ((extChartAt 𝓙 y).symm x)
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) (ψ ((extChartAt 𝓙 y).symm x))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, ℝ) ψ ((extChartAt 𝓙 y).symm x)))) :
    let β := incrementsTransversePairing F hF ((extChartAt 𝓙 y).symm x)
      (fun a : Fin m ↦ incrementsModeCoordinateDirections (extChartAt 𝓙 y).symm x a.succ)
    (β.comp β.adjoint).IsInvertible := by
  rw [incrementsModePhaseCovector_eq_chart ψ y Ω hΩ hΩt x hx hψ hadapt] at hgood
  exact incrementsModeTransverseGram_of_goodChart F hF y x (hΩt hx) hgood

/-- Domain form of the actual Good-phase bridge, matching precisely the internal
hfree argument of the accepted coefficient regularity provider. No selected lower
Gram bound is inferred. Source: local transverse freeness before (6.2). -/
theorem incrementsModeTransverseGram_on_of_goodPhase (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (ψ : M → ℝ) (y : M) (Ω : Set D)
    (hΩ : IsOpen Ω) (hΩt : Ω ⊆ (extChartAt 𝓙 y).target)
    (hψ : ∀ x ∈ Ω, MDifferentiableAt 𝓙 𝓘(ℝ, ℝ) ψ ((extChartAt 𝓙 y).symm x))
    (hadapt : ∀ z ∈ Ω, ψ ((extChartAt 𝓙 y).symm z) = z 0)
    (hgood : ∀ x ∈ Ω, GoodCovector F hF ((extChartAt 𝓙 y).symm x)
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) (ψ ((extChartAt 𝓙 y).symm x))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, ℝ) ψ ((extChartAt 𝓙 y).symm x)))) :
    ∀ x ∈ Ω,
      let β := incrementsTransversePairing F hF ((extChartAt 𝓙 y).symm x)
        (fun a : Fin m ↦ incrementsModeCoordinateDirections (extChartAt 𝓙 y).symm x a.succ)
      (β.comp β.adjoint).IsInvertible := by
  intro x hx
  exact incrementsModeTransverseGram_of_goodPhase F hF ψ y Ω hΩ hΩt x hx
    (hψ x hx) hadapt (hgood x hx)

/-- The SAME real/complex coefficient fields are smooth from ORIGINAL immersion
and actual adapted Good phase, with no beta-Gram invertibility left as an input.
Reuse all four accepted coefficient regularity proofs after the genuine bridge.
Uniform weighted/full-parameter estimates remain separate. Source: (6.2). -/
theorem incrementsModeCoefficients_contDiffOn_of_goodPhase (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (ψ : M → ℝ) (y : M) (Ω : Set D)
    (hΩ : IsOpen Ω) (hΩt : Ω ⊆ (extChartAt 𝓙 y).target)
    (hinj : ∀ x ∈ Ω, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F ((extChartAt 𝓙 y).symm x)))
    (hψ : ∀ x ∈ Ω, MDifferentiableAt 𝓙 𝓘(ℝ, ℝ) ψ ((extChartAt 𝓙 y).symm x))
    (hadapt : ∀ z ∈ Ω, ψ ((extChartAt 𝓙 y).symm z) = z 0)
    (hgood : ∀ x ∈ Ω, GoodCovector F hF ((extChartAt 𝓙 y).symm x)
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) (ψ ((extChartAt 𝓙 y).symm x))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, ℝ) ψ ((extChartAt 𝓙 y).symm x)))) :
    ContDiffOn ℝ ∞ (incrementsModeFirstOrderA (I := 𝓙) F hF (extChartAt 𝓙 y).symm) Ω ∧
    ContDiffOn ℝ ∞ (incrementsModeFirstOrderB (I := 𝓙) F hF (extChartAt 𝓙 y).symm) Ω ∧
    ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA (I := 𝓙) F hF (extChartAt 𝓙 y).symm) Ω ∧
    ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB (I := 𝓙) F hF (extChartAt 𝓙 y).symm) Ω := by
  have hfree := incrementsModeTransverseGram_on_of_goodPhase F hF ψ y Ω hΩ hΩt hψ hadapt hgood
  exact ⟨incrementsModeFirstOrderA_contDiffOn F hF y Ω hΩ hΩt hinj hfree,
    incrementsModeFirstOrderB_contDiffOn F hF y Ω hΩ hΩt hinj hfree,
    incrementsModeComplexFirstOrderA_contDiffOn F hF y Ω hΩ hΩt hinj hfree,
    incrementsModeComplexFirstOrderB_contDiffOn F hF y Ω hΩ hΩt hinj hfree⟩

end GlobalEmbedding.Paper
