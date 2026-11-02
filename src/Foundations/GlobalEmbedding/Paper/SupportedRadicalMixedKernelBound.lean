import GlobalEmbedding.Paper.SupportedRadicalNormalResidual
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!+# The same actual residual's mixed-direction kernel bound

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1009–1012 and 1027–1029. For the original affine family of operators, zero actual normal
derivative determines the mixed variation from the derivative of the recovered radical.
Evaluation injectivity therefore gives a genuine injection of that derivative kernel into
the support parameter space. No formal desired-kernel or normal-rank premise is supplied.
-/

noncomputable section
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {K U Z : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The SAME actual normal equation restricted to the original affine operator family.
Source: `prop:supported-rank`, mixed kernel graph coordinates. -/
def supportedRadicalMixedEquation (a : U ≃L[ℝ] (K →L[ℝ] ℝ))
    (r : (ℝ × U) →L[ℝ] ℝ) (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U)))
    (J : Z →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (Y : K →L[ℝ] Z) : K →L[ℝ] r.ker :=
  supportedRadicalNormalResidual a r w hw (Q + J.comp Y)

/-- The SAME affine operator family has the actual normal derivative, including the
recovered-radical term. This exposes the completed chain-rule proof for the original
kernel-chart consumer, rather than repeating it. Source: `prop:supported-rank`, (9.4). -/
theorem supportedRadicalMixedEquation_fderiv_apply
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r Q) = 0)
    (J : Z →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (Y : K →L[ℝ] Z) (k : K) :
    (((fderiv ℝ (supportedRadicalMixedEquation a r w hw Q J) 0 Y) k : r.ker) : ℝ × U) =
      J (Y k) (1, 0) + Q k (0, -e.symm (supportedRadicalRows a r (J.comp Y) (1, 0))) := by
  let C : (K →L[ℝ] Z) →L[ℝ] (K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) :=
    ContinuousLinearMap.compL ℝ K Z ((ℝ × U) →L[ℝ] (ℝ × U)) J
  let G : (K →L[ℝ] Z) →L[ℝ] U :=
    -(e.symm : U →L[ℝ] U).comp ((ContinuousLinearMap.apply ℝ U (1, 0)).comp
      ((supportedRadicalRows a r).comp C))
  let f := supportedRadicalMixedEquation a r w hw Q J
  have hlin : HasFDerivAt (fun Y : K →L[ℝ] Z ↦ C Y) C (0 : K →L[ℝ] Z) := by
    simpa using! (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      (E := K →L[ℝ] Z) (F := K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) C
      (x := (0 : K →L[ℝ] Z)))
  have hparam : HasFDerivAt (fun Y : K →L[ℝ] Z ↦ Q + C Y) C 0 := by
    simpa using! (HasFDerivAt.const_add (𝕜 := ℝ) (E := K →L[ℝ] Z)
      (F := K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) Q hlin)
  have hnormal := (supportedRadicalNormalResidual_contDiffAt a r w hw Q e hA).differentiableAt
    (by simp)
  have hb : Q + C (0 : K →L[ℝ] Z) = Q := by
    apply ContinuousLinearMap.ext
    intro k
    apply ContinuousLinearMap.ext
    intro v
    change Q k v + J (0 : Z) v = Q k v
    have hzero : J (0 : Z) v = 0 :=
      congrArg (fun L : (ℝ × U) →L[ℝ] (ℝ × U) ↦ L v) J.map_zero
    rw [hzero]
    exact add_zero _
  have hn : HasFDerivAt (supportedRadicalNormalResidual a r w hw)
      (fderiv ℝ (supportedRadicalNormalResidual a r w hw) Q)
      (Q + C (0 : K →L[ℝ] Z)) := by
    rw [hb]
    exact hnormal.hasFDerivAt
  have hd : HasFDerivAt f
      ((fderiv ℝ (supportedRadicalNormalResidual a r w hw) Q).comp C) 0 := by
    simpa [f, supportedRadicalMixedEquation, C] using!
      (HasFDerivAt.comp (𝕜 := ℝ) (E := K →L[ℝ] Z)
        (F := K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (G := K →L[ℝ] r.ker)
        (0 : K →L[ℝ] Z) hn hparam)
  have hdf (Y : K →L[ℝ] Z) (k : K) :
      (((fderiv ℝ f 0 Y) k : r.ker) : ℝ × U) = J (Y k) (1, 0) + Q k (0, G Y) := by
    rw [hd.fderiv]
    rw [ContinuousLinearMap.comp_apply,
      supportedRadicalNormalResidual_fderiv_apply a r w hw Q e hA hC (C Y) k]
    simp [C, G]
  exact hdf Y k

/-- The actual kernel of the SAME residual derivative injects into the support parameter
space. Proof: if two kernel elements have the same recovered radical derivative, the true
product-rule formula gives the same evaluation of their mixed variations at the radical.
The actual mixed evaluation is injective, so the variations agree. Native dimension
monotonicity yields the bound. Source: `prop:supported-rank`, moving-support dimension loss. -/
theorem supportedRadicalMixedEquation_kernel_finrank_le
    [FiniteDimensional ℝ K] [FiniteDimensional ℝ U] [FiniteDimensional ℝ Z]
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r Q) = 0)
    (J : Z →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U)))
    (hJ : Function.Injective (fun z : Z ↦ J z (1, 0))) :
    Module.finrank ℝ (fderiv ℝ (supportedRadicalMixedEquation a r w hw Q J) 0).ker ≤
      Module.finrank ℝ U := by
  let C : (K →L[ℝ] Z) →L[ℝ] (K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) :=
    ContinuousLinearMap.compL ℝ K Z ((ℝ × U) →L[ℝ] (ℝ × U)) J
  let G : (K →L[ℝ] Z) →L[ℝ] U :=
    -(e.symm : U →L[ℝ] U).comp ((ContinuousLinearMap.apply ℝ U (1, 0)).comp
      ((supportedRadicalRows a r).comp C))
  let f := supportedRadicalMixedEquation a r w hw Q J
  have hdf (Y : K →L[ℝ] Z) (k : K) :
      (((fderiv ℝ f 0 Y) k : r.ker) : ℝ × U) = J (Y k) (1, 0) + Q k (0, G Y) := by
    exact supportedRadicalMixedEquation_fderiv_apply a r w hw Q e hA hC J Y k
  let g : (fderiv ℝ f 0).ker →ₗ[ℝ] U :=
    G.toLinearMap.comp (fderiv ℝ f 0).ker.subtype
  have hg : Function.Injective g := by
    intro x y hxy
    have hG : G x.val = G y.val := hxy
    have hx : fderiv ℝ f 0 x.val = 0 := x.property
    have hy : fderiv ℝ f 0 y.val = 0 := y.property
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro k
    apply hJ
    have hx0 : J (x.val k) (1, 0) + Q k (0, G x.val) = 0 := by
      rw [← hdf x.val k, hx]
      rfl
    have hy0 : J (y.val k) (1, 0) + Q k (0, G y.val) = 0 := by
      rw [← hdf y.val k, hy]
      rfl
    rw [hG] at hx0
    exact add_right_cancel (hx0.trans hy0.symm)
  exact LinearMap.finrank_le_finrank_of_injective hg

end GlobalEmbedding.Paper
