import Initialization.Assembly.SelectorHopfDerivative
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The actual second derivative of the same selected sphere-valued map

This bridge works directly with a genuine map into the native sphere product.
It only needs the smooth germ of its literal ambient inclusion, so it also
applies to chart pullbacks without asserting a false global support property
for an inverse chart outside its target.
-/

noncomputable section
open Set Function
open scoped ContDiff Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} (C : Fin n → ℕ)
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def selectorSourceAmbient (z : E → FreeHopfProduct C) : E → HopfProductAmbient C :=
  hopfProductInclusion C ∘ z

def selectorSourceIdealAmbient (z : E → FreeHopfProduct C)
    (r : E → Fin n → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] HopfProductAmbient C :=
  ∑ i, (r x i).smulRight (ambientHopfGenerator C i (z x))

def selectorSourceAmbientError (z : E → FreeHopfProduct C)
    (r : E → Fin n → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] HopfProductAmbient C :=
  fderiv ℝ (selectorSourceAmbient C z) x - selectorSourceIdealAmbient C z r x

def selectorSourceIdealFirst (S : FreeHopfProduct C → F) (z : E → FreeHopfProduct C)
    (r : E → Fin n → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] F :=
  ∑ i, (r x i).smulRight (freeHopfDeriv C i S (z x))

def selectorSourceFirstError (S : FreeHopfProduct C → F) (z : E → FreeHopfProduct C)
    (r : E → Fin n → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] F :=
  fderiv ℝ (S ∘ z) x - selectorSourceIdealFirst C S z r x

variable [∀ i, Fact (0 < C i)]

/-- The literal selected map has the ordinary chain-rule derivative through
the genuine ambient extension at the same sphere-product argument. -/
theorem selectorSource_fderiv
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct C) {x : E}
    (hz : DifferentiableAt ℝ (selectorSourceAmbient C z) x) :
    fderiv ℝ (S ∘ z) x =
      (fderiv ℝ (selectorAmbientExtension C S) (selectorSourceAmbient C z x)).comp
        (fderiv ℝ (selectorSourceAmbient C z) x) := by
  have he : S ∘ z = selectorAmbientExtension C S ∘ selectorSourceAmbient C z := by
    funext y
    exact (selectorAmbientExtension_inclusion C S (z y)).symm
  rw [he]
  exact fderiv_comp x
    ((selectorAmbientExtension_contDiffAt C S hS
      (hopfProductInclusion_mem_radial C (z x))).differentiableAt (by simp)) hz

/-- The error of the actual selected map is exactly the same fixed derivative
of S applied to the actual ambient error. No abstract first jet is an input. -/
theorem selectorSourceFirstError_eq_comp
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct C) (r : E → Fin n → E →L[ℝ] ℝ)
    {x : E} (hz : DifferentiableAt ℝ (selectorSourceAmbient C z) x) :
    selectorSourceFirstError C S z r x =
      (fderiv ℝ (selectorAmbientExtension C S) (selectorSourceAmbient C z x)).comp
        (selectorSourceAmbientError C z r x) := by
  have hi : selectorSourceIdealFirst C S z r x =
      (fderiv ℝ (selectorAmbientExtension C S) (selectorSourceAmbient C z x)).comp
        (selectorSourceIdealAmbient C z r x) := by
    ext v
    simp only [selectorSourceIdealFirst, selectorSourceIdealAmbient, sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]
    exact (selectorAmbientExtension_ideal_velocity C S hS (z x) (fun i ↦ r x i v)).symm
  rw [selectorSourceFirstError, selectorSource_fderiv C S hS z hz, hi,
    selectorSourceAmbientError, ContinuousLinearMap.comp_sub]

theorem selectorSource_contDiffAt
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct C) {x : E}
    (hz : ContDiffAt ℝ ∞ (selectorSourceAmbient C z) x) :
    ContDiffAt ℝ ∞ (S ∘ z) x := by
  have h : S ∘ z = selectorAmbientExtension C S ∘ selectorSourceAmbient C z := by
    funext y
    exact (selectorAmbientExtension_inclusion C S (z y)).symm
  rw [h]
  exact (selectorAmbientExtension_contDiffAt C S hS
    (hopfProductInclusion_mem_radial C (z x))).comp x hz

theorem selectorSource_hopf_contDiffAt
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct C) {x : E}
    (hz : ContDiffAt ℝ ∞ (selectorSourceAmbient C z) x) (i : Fin n) :
    ContDiffAt ℝ ∞ (freeHopfDeriv C i S ∘ z) x :=
  selectorSource_contDiffAt C _
    (contMDiff_orbitDeriv (freeHopfProductFlow C i)
      (freeHopfProductFlow_contMDiff C i) S hS) z hz

/-- The derivative of each literal Hopf column has the expected second-Hopf
main term and a remainder containing the actual ambient first-jet error. -/
theorem selectorSource_hopf_fderiv
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct C) (r : E → Fin n → E →L[ℝ] ℝ)
    {x : E} (hz : DifferentiableAt ℝ (selectorSourceAmbient C z) x)
    (i : Fin n) (v : E) :
    fderiv ℝ (freeHopfDeriv C i S ∘ z) x v =
      (∑ j, r x j v • freeHopfDeriv C j (freeHopfDeriv C i S) (z x)) +
      fderiv ℝ (selectorAmbientExtension C (freeHopfDeriv C i S))
        (selectorSourceAmbient C z x) (selectorSourceAmbientError C z r x v) := by
  have hs : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ (freeHopfDeriv C i S) :=
    contMDiff_orbitDeriv (freeHopfProductFlow C i)
      (freeHopfProductFlow_contMDiff C i) S hS
  have he : freeHopfDeriv C i S ∘ z =
      selectorAmbientExtension C (freeHopfDeriv C i S) ∘ selectorSourceAmbient C z := by
    funext y
    exact (selectorAmbientExtension_inclusion C _ (z y)).symm
  rw [he, fderiv_comp x
    ((selectorAmbientExtension_contDiffAt C _ hs
      (hopfProductInclusion_mem_radial C (z x))).differentiableAt (by simp)) hz]
  have hd : fderiv ℝ (selectorSourceAmbient C z) x v =
      selectorSourceIdealAmbient C z r x v + selectorSourceAmbientError C z r x v := by
    simp only [selectorSourceAmbientError, sub_apply]
    abel
  rw [ContinuousLinearMap.comp_apply, hd, map_add]
  congr 1
  simp only [selectorSourceIdealAmbient, sum_apply, ContinuousLinearMap.smulRight_apply]
  change fderiv ℝ (selectorAmbientExtension C (freeHopfDeriv C i S))
    (hopfProductInclusion C (z x))
      (∑ j, r x j v • ambientHopfGenerator C j (z x)) = _
  exact selectorAmbientExtension_ideal_velocity C _ hs (z x) (fun j ↦ r x j v)

variable [FiniteDimensional ℝ E]

theorem selectorSourceIdealFirst_contDiffAt
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct C) (r : E → Fin n → E →L[ℝ] ℝ)
    {x : E} (hz : ContDiffAt ℝ ∞ (selectorSourceAmbient C z) x)
    (hr : ∀ i, ContDiffAt ℝ ∞ (fun y ↦ r y i) x) :
    ContDiffAt ℝ ∞ (selectorSourceIdealFirst C S z r) x := by
  change ContDiffAt ℝ ∞ (fun y ↦ ∑ i,
    (r y i).smulRight (freeHopfDeriv C i S (z y))) x
  apply ContDiffAt.sum
  intro i _
  exact (((ContinuousLinearMap.smulRightL ℝ E F).contDiff.contDiffAt).comp x (hr i)).clm_apply
    (selectorSource_hopf_contDiffAt C S hS z hz i)

theorem selectorSourceFirstError_contDiffAt
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct C) (r : E → Fin n → E →L[ℝ] ℝ)
    {x : E} (hz : ContDiffAt ℝ ∞ (selectorSourceAmbient C z) x)
    (hr : ∀ i, ContDiffAt ℝ ∞ (fun y ↦ r y i) x) :
    ContDiffAt ℝ ∞ (selectorSourceFirstError C S z r) x :=
  ((selectorSource_contDiffAt C S hS z hz).fderiv_right (m := ∞) (by simp)).sub
    (selectorSourceIdealFirst_contDiffAt C S hS z r hz hr)

/-- The second derivative is Lean's derivative of the actual first derivative.
Its main term is the genuine Hopf Hessian with the same rates, its rate-derivative
term is tangent, and the other two terms contain actual first-jet errors. -/
theorem selectorSource_second_fderiv
    (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct C) (r : E → Fin n → E →L[ℝ] ℝ)
    {x : E} (hz : ContDiffAt ℝ ∞ (selectorSourceAmbient C z) x)
    (hr : ∀ i, ContDiffAt ℝ ∞ (fun y ↦ r y i) x) (v w : E) :
    fderiv ℝ (fderiv ℝ (S ∘ z)) x v w =
      (∑ i, (r x i w) •
        (∑ j, (r x j v) • freeHopfDeriv C j (freeHopfDeriv C i S) (z x))) +
      (∑ i, (fderiv ℝ (fun y ↦ r y i) x v w) • freeHopfDeriv C i S (z x)) +
      (∑ i, (r x i w) •
        (fderiv ℝ (selectorAmbientExtension C (freeHopfDeriv C i S))
          (selectorSourceAmbient C z x) (selectorSourceAmbientError C z r x v))) +
      fderiv ℝ (selectorSourceFirstError C S z r) x v w := by
  classical
  have hJ := (selectorSourceIdealFirst_contDiffAt C S hS z r hz hr).differentiableAt
    (by simp)
  have hR := (selectorSourceFirstError_contDiffAt C S hS z r hz hr).differentiableAt
    (by simp)
  have he : fderiv ℝ (S ∘ z) =
      selectorSourceIdealFirst C S z r + selectorSourceFirstError C S z r := by
    funext y
    simp only [Pi.add_apply, selectorSourceFirstError]
    abel
  rw [he, fderiv_add hJ hR]
  simp only [add_apply]
  congr 1
  have heval (A : E → E →L[ℝ] F) (hA : DifferentiableAt ℝ A x) :
      fderiv ℝ (fun y ↦ A y w) x v = fderiv ℝ A x v w := by
    have h := hA.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    have h' : fderiv ℝ (fun y ↦ A y w) x = (fderiv ℝ A x).flip w := by
      simpa only [ContinuousLinearMap.comp_zero, zero_add] using h.fderiv
    exact congrArg (fun D : E →L[ℝ] F ↦ D v) h'
  rw [← heval _ hJ]
  simp only [selectorSourceIdealFirst, sum_apply, ContinuousLinearMap.smulRight_apply]
  have hri (i : Fin n) : DifferentiableAt ℝ (fun y ↦ r y i w) x :=
    ((hr i).clm_apply contDiffAt_const).differentiableAt (by simp)
  have hYi (i : Fin n) : DifferentiableAt ℝ (freeHopfDeriv C i S ∘ z) x :=
    (selectorSource_hopf_contDiffAt C S hS z hz i).differentiableAt (by simp)
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun i y ↦ r y i w • freeHopfDeriv C i S (z y))
    (fun i _ ↦ (hri i).smul (hYi i))]
  simp only [sum_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hsm := congrArg (fun D : E →L[ℝ] F ↦ D v)
    ((hri i).hasFDerivAt.smul (hYi i).hasFDerivAt).fderiv
  simp only [Function.comp_def, Pi.smul_def', add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply] at hsm
  rw [hsm]
  have hriEval : fderiv ℝ (fun y ↦ r y i w) x v =
      fderiv ℝ (fun y ↦ r y i) x v w := by
    have h := ((hr i).differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const w x)
    have h' : fderiv ℝ (fun y ↦ r y i w) x =
        (fderiv ℝ (fun y ↦ r y i) x).flip w := by
      simpa only [ContinuousLinearMap.comp_zero, zero_add] using h.fderiv
    exact congrArg (fun D : E →L[ℝ] ℝ ↦ D v) h'
  have hcol := selectorSource_hopf_fderiv C S hS z r
    (hz.differentiableAt (by simp)) i v
  simp only [Function.comp_def] at hcol
  rw [hriEval, hcol, smul_add]
  abel

end GlobalEmbedding.Initialization
