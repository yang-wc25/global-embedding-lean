import GlobalEmbedding.Paper.IncrementsModeCoordinateRegularity
import GlobalEmbedding.Paper.IncrementsModeAmbientTransverseFrame
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# SAME original real and complex mode coefficients are smooth

Source: `main.tex`, lem:increments, (6.2), lines 617–643.
DAG: `increments-mode-coefficient-regularity`. Exclusive worker W2.
All coefficient regularity follows from original local immersion/free geometry.
Uniform weighted coefficient bounds and parameter/geometry uniformity remain open.
-/

noncomputable section
open Manifold Set
open scoped ContDiff
namespace GlobalEmbedding.Paper

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "P" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ P
local notation "Cdata" => Fin (m + 1) → ℂ

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]
  (F : M → EuclideanSpace ℝ (Fin N))
  (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (y : M)
  (Ω : Set (EuclideanSpace ℝ (Fin (m + 1)))) (hΩ : IsOpen Ω)
  (hΩt : Ω ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) y).target)
  (hinj : ∀ x ∈ Ω, Function.Injective
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) y).symm x)))

include hF hΩ hΩt hinj

/-- The SAME actual ambient transverse column frame is smooth from the original
true-B rows, by native finite-domain operator evaluation. Source: J in (6.2). -/
theorem incrementsModeAmbientTransverseFrame_contDiffOn :
    ContDiffOn ℝ ∞
      (incrementsModeAmbientTransverseFrame (I := 𝓙) F hF (extChartAt 𝓙 y).symm) Ω := by
  apply contDiffOn_clm_apply.mpr
  intro t
  have hs : ContDiffOn ℝ ∞ (fun x ↦ ∑ q : P,
      t q • (incrementsModeSecondForm (I := 𝓙) F hF (extChartAt 𝓙 y).symm x
        q.val.1.succ q.val.2.succ : V)) Ω := by
    exact ContDiffOn.sum fun q _ ↦
      (incrementsModeSecondForm_contDiffOn F hF y Ω hΩ hΩt hinj
        q.val.1.succ q.val.2.succ).const_smul (t q)
  simpa [incrementsModeAmbientTransverseFrame] using hs

/-- Actual value part of T is smooth from original induced Gamma.
Source: T in (6.2); no transverse coefficient output is assumed. -/
theorem incrementsModeTransverseValue_contDiffOn :
    ContDiffOn ℝ ∞ (incrementsModeTransverseValue F (extChartAt 𝓙 y).symm) Ω := by
  apply contDiffOn_clm_apply.mpr
  intro u
  have hr : ContDiffOn ℝ ∞ (fun x (q : P) ↦
      -inner ℝ (incrementsModeGamma F (extChartAt 𝓙 y).symm x
        q.val.1.succ q.val.2.succ) u) Ω := by
    apply contDiffOn_pi.mpr
    intro q
    exact ((incrementsModeGamma_contDiffOn F hF y Ω hΩ hΩt hinj
      q.val.1.succ q.val.2.succ).inner ℝ contDiffOn_const).neg
  exact (EuclideanSpace.equiv P ℝ).symm.contDiff.comp_contDiffOn hr

variable (hfree : ∀ x ∈ Ω,
  ((incrementsTransversePairing (m := m)
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))) F hF
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) y).symm x)
    (fun a : Fin m ↦ incrementsModeCoordinateDirections (m := m)
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) y).symm x a.succ)).comp
    (incrementsTransversePairing (m := m)
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))) F hF
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) y).symm x)
      (fun a : Fin m ↦
        incrementsModeCoordinateDirections (m := m)
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))))
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) y).symm x a.succ)).adjoint).IsInvertible)

include hfree

/-- ORIGINAL local beta-Gram freeness gives smoothness of the SAME ambient J.
Accepted actual frame Gram regularity applies after the proved exact J adapter.
Source: original J in (6.2), not a desired coefficient smoothness premise. -/
theorem incrementsModeAmbientJ_contDiffOn :
    ContDiffOn ℝ ∞ (fun x ↦
      freeGramRightInverse
        (incrementsModeAmbientTransverseFrame (I := 𝓙) F hF (extChartAt 𝓙 y).symm x))
      Ω := by
  have hC := incrementsModeAmbientTransverseFrame_contDiffOn F hF y Ω hΩ hΩt hinj
  have hi : ∀ x ∈ Ω, Function.Injective
      (incrementsModeAmbientTransverseFrame (I := 𝓙) F hF (extChartAt 𝓙 y).symm x) := by
    intro x hx
    exact incrementsModeAmbientTransverseFrame_injective (I := 𝓙) F hF (extChartAt 𝓙 y).symm x
      (hfree x hx)
  exact (freeGramRightInverse_contMDiffOn (I := 𝓙) _ hC.contMDiffOn hi).contDiffOn

/-- SAME actual first-jet A is smooth from ORIGINAL smooth immersion/free geometry.
Use the exact ambient J, native row inner products and finite operator evaluation.
Source: A in the actual first-order realization of (6.2). -/
theorem incrementsModeFirstOrderA_contDiffOn :
    ContDiffOn ℝ ∞ (incrementsModeFirstOrderA (I := 𝓙) F hF (extChartAt 𝓙 y).symm) Ω := by
  have hR := incrementsModeAmbientJ_contDiffOn F hF y Ω hΩ hΩt hinj hfree
  apply contDiffOn_clm_apply.mpr
  intro jet
  let d : Fin (m + 1) → ℝ := Fin.cases ((jet (EuclideanSpace.single 0 1)) 0)
    (fun a ↦ (jet (EuclideanSpace.single 0 1)) a.succ +
      (jet (EuclideanSpace.single a.succ 1)) 0)
  let rows : D → Fin (m + 1) → ℝ := fun x i ↦ d i - incrementsModeRowWeight i *
    inner ℝ (incrementsModeSecondForm (I := 𝓙) F hF (extChartAt 𝓙 y).symm x 0 i : V)
      (freeGramRightInverse
        (incrementsModeAmbientTransverseFrame (I := 𝓙) F hF (extChartAt 𝓙 y).symm x)
        (incrementsModeTransverseJet jet))
  have hr : ContDiffOn ℝ ∞ rows Ω := by
    apply contDiffOn_pi.mpr
    intro i
    exact contDiffOn_const.sub (contDiffOn_const.mul
      ((incrementsModeSecondForm_contDiffOn F hF y Ω hΩ hΩt hinj 0 i).inner ℝ
        (hR.clm_apply contDiffOn_const)))
  have hd := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.contDiff.comp_contDiffOn hr
  apply hd.congr
  intro x hx
  have hJ := incrementsModeCoordinateJ_ambient_apply (I := 𝓙) F hF (extChartAt 𝓙 y).symm x
    (incrementsModeTransverseJet jet)
  ext i
  refine Fin.cases ?_ (fun a ↦ ?_) i
  · change (jet (EuclideanSpace.single 0 1)) 0 - incrementsModeRowWeight 0 *
        inner ℝ (incrementsModeSecondForm (I := 𝓙) F hF (extChartAt 𝓙 y).symm x 0 0 : V)
          (incrementsModeCoordinateJ (I := 𝓙) F hF (extChartAt 𝓙 y).symm x
            (incrementsModeTransverseJet jet) : V) = _
    rw [hJ]
    rfl
  · change ((jet (EuclideanSpace.single 0 1)) a.succ +
        (jet (EuclideanSpace.single a.succ 1)) 0) - incrementsModeRowWeight a.succ *
        inner ℝ (incrementsModeSecondForm (I := 𝓙) F hF (extChartAt 𝓙 y).symm x 0 a.succ : V)
          (incrementsModeCoordinateJ (I := 𝓙) F hF (extChartAt 𝓙 y).symm x
            (incrementsModeTransverseJet jet) : V) = _
    rw [hJ]
    rfl

/-- SAME actual zeroth-order B is smooth from ORIGINAL local geometry.
The value part T and exact included J are genuine proved geometric outputs.
Source: B in the actual first-order realization of (6.2). -/
theorem incrementsModeFirstOrderB_contDiffOn :
    ContDiffOn ℝ ∞ (incrementsModeFirstOrderB (I := 𝓙) F hF (extChartAt 𝓙 y).symm) Ω := by
  have hR := incrementsModeAmbientJ_contDiffOn F hF y Ω hΩ hΩt hinj hfree
  have hT := incrementsModeTransverseValue_contDiffOn F hF y Ω hΩ hΩt hinj
  apply contDiffOn_clm_apply.mpr
  intro u
  let rows : D → Fin (m + 1) → ℝ := fun x i ↦
    -(incrementsModeRowWeight i *
      inner ℝ (incrementsModeGamma F (extChartAt 𝓙 y).symm x 0 i) u) -
    incrementsModeRowWeight i *
      inner ℝ (incrementsModeSecondForm (I := 𝓙) F hF (extChartAt 𝓙 y).symm x 0 i : V)
        (freeGramRightInverse
          (incrementsModeAmbientTransverseFrame (I := 𝓙) F hF (extChartAt 𝓙 y).symm x)
          (incrementsModeTransverseValue F (extChartAt 𝓙 y).symm x u))
  have hr : ContDiffOn ℝ ∞ rows Ω := by
    apply contDiffOn_pi.mpr
    intro i
    exact (contDiffOn_const.mul
      ((incrementsModeGamma_contDiffOn F hF y Ω hΩ hΩt hinj 0 i).inner ℝ
        contDiffOn_const)).neg.sub
      (contDiffOn_const.mul
        ((incrementsModeSecondForm_contDiffOn F hF y Ω hΩ hΩt hinj 0 i).inner ℝ
          (hR.clm_apply (hT.clm_apply contDiffOn_const))))
  have hd := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.contDiff.comp_contDiffOn hr
  apply hd.congr
  intro x hx
  have hJ := incrementsModeCoordinateJ_ambient_apply (I := 𝓙) F hF (extChartAt 𝓙 y).symm x
    (incrementsModeTransverseValue F (extChartAt 𝓙 y).symm x u)
  ext i
  change -(incrementsModeRowWeight i *
      inner ℝ (incrementsModeGamma F (extChartAt 𝓙 y).symm x 0 i) u) -
    incrementsModeRowWeight i *
      inner ℝ (incrementsModeSecondForm (I := 𝓙) F hF (extChartAt 𝓙 y).symm x 0 i : V)
        (incrementsModeCoordinateJ (I := 𝓙) F hF (extChartAt 𝓙 y).symm x
          (incrementsModeTransverseValue F (extChartAt 𝓙 y).symm x u) : V) = _
  rw [hJ]
  rfl

/-- SAME actual complex B is smooth by its ORIGINAL native real/imaginary component
formula and the proved genuine real coefficient regularity. Source: (6.2). -/
theorem incrementsModeComplexFirstOrderB_contDiffOn :
    ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB (I := 𝓙) F hF (extChartAt 𝓙 y).symm) Ω := by
  have hB := incrementsModeFirstOrderB_contDiffOn F hF y Ω hΩ hΩt hinj hfree
  exact ((contDiffOn_const.clm_comp (hB.clm_comp contDiffOn_const)).add
    ((contDiffOn_const.clm_comp (hB.clm_comp contDiffOn_const)).const_smul Complex.I))

/-- SAME actual complex A is smooth on the ORIGINAL localfree domain.
Only native fixed channel-jet composition is used after real coefficient regularity.
Source: (6.2); weighted geometry/parameter bounds remain separate. -/
theorem incrementsModeComplexFirstOrderA_contDiffOn :
    ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA (I := 𝓙) F hF (extChartAt 𝓙 y).symm) Ω := by
  have hA := incrementsModeFirstOrderA_contDiffOn F hF y Ω hΩ hΩt hinj hfree
  exact (((contDiffOn_const.clm_comp hA).clm_comp contDiffOn_const).add
    (((contDiffOn_const.clm_comp hA).clm_comp contDiffOn_const).const_smul Complex.I))

end GlobalEmbedding.Paper
