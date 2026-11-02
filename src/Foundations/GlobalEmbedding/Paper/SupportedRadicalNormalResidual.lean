import GlobalEmbedding.Paper.SupportedRadicalGraphChart

/-!+# The actual radical residual in its fixed normal-equation space

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1012. The full common-radical residual satisfies its scalar row equations. Project
it to the fixed kernel of that scalar test without changing its zeros. The resulting actual
normal equation has the correct finite target, before the final literal supported-kernel
and surjective-differential consumers. No desired geometry is supplied as a premise.
-/

noncomputable section

open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {K U : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- The actual projection to a scalar kernel along an actual scalar section.
Source: `prop:supported-rank`, fixed normal-equation coordinates. -/
def supportedRadicalScalarProjection (r : (ℝ × U) →L[ℝ] ℝ) (w : ℝ × U)
    (hw : r w = 1) : (ℝ × U) →L[ℝ] r.ker :=
  (ContinuousLinearMap.id ℝ (ℝ × U) - r.smulRight w).codRestrict r.ker (by
    intro v
    change r (v - r v • w) = 0
    simp [hw])

/-- The actual normal residual, in the fixed scalar-test kernel.
Source: `prop:supported-rank`, local defining equations. -/
def supportedRadicalNormalResidual (a : U ≃L[ℝ] (K →L[ℝ] ℝ))
    (r : (ℝ × U) →L[ℝ] ℝ) (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) : K →L[ℝ] r.ker :=
  (supportedRadicalScalarProjection r w hw).comp (supportedRadicalResidual a r Q)

/-- The full actual residual satisfies every scalar row equation on the true chart domain.
Source: `prop:supported-rank`, exact common-radical row recovery. -/
theorem supportedRadicalResidual_scalar_eq_zero (a : U ≃L[ℝ] (K →L[ℝ] ℝ))
    (r : (ℝ × U) →L[ℝ] ℝ) (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U)))
    (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U))
    (k : K) : r (supportedRadicalResidual a r Q k) = 0 := by
  have hrow : supportedRadicalRows a r Q (supportedRadicalVector a r Q) = 0 :=
    (supportedKernel_mem_kernel_iff (supportedRadicalRows a r Q) e hA 1
      (supportedRadicalCoordinate a r Q)).mpr rfl
  have h := congrArg (fun u : U ↦ a u k) hrow
  simpa [supportedRadicalRows_apply, supportedRadicalResidual] using h

/-- The actual normal residual has exactly the full residual's zeros on its true domain.
Proof: the scalar row is zero, so the scalar-section projection leaves each vector unchanged.
Source: `prop:supported-rank`, exact local defining zero set. -/
theorem supportedRadicalNormalResidual_eq_zero_iff (a : U ≃L[ℝ] (K →L[ℝ] ℝ))
    (r : (ℝ × U) →L[ℝ] ℝ) (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U)) :
    supportedRadicalNormalResidual a r w hw Q = 0 ↔ supportedRadicalResidual a r Q = 0 := by
  constructor
  · intro hzero
    apply ContinuousLinearMap.ext
    intro k
    have h := congrArg (fun L : K →L[ℝ] r.ker ↦ ((L k : r.ker) : ℝ × U)) hzero
    have hr := supportedRadicalResidual_scalar_eq_zero a r Q e hA k
    simpa [supportedRadicalNormalResidual, supportedRadicalScalarProjection, hr] using h
  · intro hzero
    simp [supportedRadicalNormalResidual, hzero]

/-- The actual normal residual is smooth on the genuine invertible-block chart.
Source: `prop:supported-rank`, smooth local normal equations. -/
theorem supportedRadicalNormalResidual_contDiffAt [CompleteSpace U]
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U)) :
    ContDiffAt ℝ ∞ (supportedRadicalNormalResidual a r w hw) Q := by
  exact (contDiffAt_const (c := supportedRadicalScalarProjection r w hw)).clm_comp
    (supportedRadicalResidual_contDiffAt a r Q e hA)

/-- The true linearized vector residual lies in the fixed scalar kernel.
Proof: the scalar block equation cancels its two product-rule terms exactly.
Source: `prop:supported-rank`, actual normal differential. -/
theorem supportedRadicalDerivative_scalar_eq_zero (a : U ≃L[ℝ] (K →L[ℝ] ℝ))
    (r : (ℝ × U) →L[ℝ] ℝ) (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U)))
    (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U))
    (Δ : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (k : K) :
    r (Δ k (1, 0) + Q k (0, -e.symm (supportedRadicalRows a r Δ (1, 0)))) = 0 := by
  have hright (u : U) : r (Q k (0, u)) = a (e u) k := by
    rw [← supportedRadicalRows_apply a r Q (0, u) k]
    change a (supportedKernelRightBlock (supportedRadicalRows a r Q) u) k = _
    rw [hA]
    rfl
  rw [map_add, hright]
  simp [supportedRadicalRows_apply]

/-- The normal residual's actual derivative is exactly the full vector derivative, viewed in
the scalar kernel. Source: `prop:supported-rank`, local normal-coordinate derivative. -/
theorem supportedRadicalNormalResidual_fderiv_apply [CompleteSpace U]
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r Q) = 0)
    (Δ : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (k : K) :
    (((fderiv ℝ (supportedRadicalNormalResidual a r w hw) Q Δ) k : r.ker) : ℝ × U) =
      Δ k (1, 0) + Q k (0, -e.symm (supportedRadicalRows a r Δ (1, 0))) := by
  have hd := (hasFDerivAt_const (x := Q)
    (c := supportedRadicalScalarProjection r w hw)).clm_comp
      ((supportedRadicalResidual_contDiffAt a r Q e hA).differentiableAt (by simp)).hasFDerivAt
  change HasFDerivAt (supportedRadicalNormalResidual a r w hw) _ Q at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_zero, add_zero]
  change (fderiv ℝ (supportedRadicalResidual a r) Q Δ) k -
    r ((fderiv ℝ (supportedRadicalResidual a r) Q Δ) k) • w = _
  rw [supportedRadicalResidual_fderiv_apply a r Q e hA hC Δ k,
    supportedRadicalDerivative_scalar_eq_zero a r Q e hA Δ k]
  simp only [zero_smul, sub_zero]

/-- In the full actual operator-family space the normal residual is a genuine submersion.
Proof: for a prescribed scalar-kernel-valued family `T`, vary the operators by
`Δ(k)(t,u)=t*T(k)`. Its scalar rows vanish and its actual normal derivative is exactly `T`.
The supported-kernel consumer must still realize the requisite variations in its literal
symmetric-kernel graph, rather than assuming that realization. Source: `prop:supported-rank`,
finite normal-coordinate submersion construction. -/
theorem supportedRadicalNormalResidual_fderiv_surjective [CompleteSpace U]
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r Q) = 0) :
    Function.Surjective (fderiv ℝ (supportedRadicalNormalResidual a r w hw) Q) := by
  intro T
  let Δ : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U)) :=
    (ContinuousLinearMap.smulRightL ℝ (ℝ × U) (ℝ × U)
      (ContinuousLinearMap.fst ℝ ℝ U)).comp (r.ker.subtypeL.comp T)
  have hrows : supportedRadicalRows a r Δ (1, 0) = 0 := by
    apply a.injective
    ext k
    rw [supportedRadicalRows_apply]
    simp [Δ]
  refine ⟨Δ, ?_⟩
  apply ContinuousLinearMap.ext
  intro k
  apply Subtype.ext
  rw [supportedRadicalNormalResidual_fderiv_apply a r w hw Q e hA hC Δ k]
  simp [hrows, Δ]
  exact (Q k).map_zero

end GlobalEmbedding.Paper
