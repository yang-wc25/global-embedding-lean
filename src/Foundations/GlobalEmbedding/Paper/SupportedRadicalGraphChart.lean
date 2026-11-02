import GlobalEmbedding.Paper.SupportedKernelBlockChart
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!+# Actual scalar-row coordinates for a common radical

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1006. A good square block of scalar row tests recovers the radical line in a fixed
affine chart. Its full vector residual vanishes exactly when a common radical exists. These
are actual operator formulas using the accepted kernel-block chart, not assumed flag geometry.
-/

noncomputable section

open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {K U : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- The actual scalar row operator, transported by the fixed good row isomorphism.
Source: `prop:supported-rank`, local recovery of the common radical. -/
def supportedRadicalRows (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ) :
    (K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) →L[ℝ] ((ℝ × U) →L[ℝ] U) :=
  (ContinuousLinearMap.compL ℝ (ℝ × U) (K →L[ℝ] ℝ) U a.symm).comp
    ((ContinuousLinearMap.compL ℝ (ℝ × U) (K →L[ℝ] (ℝ × U)) (K →L[ℝ] ℝ)
      (ContinuousLinearMap.compL ℝ K (ℝ × U) ℝ r)).comp
      (ContinuousLinearMap.flipₗᵢ ℝ K (ℝ × U) (ℝ × U)).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The scalar rows evaluate the original actual operator family without a normalization factor.
Source: `prop:supported-rank`, scalar tests of the kernel equations. -/
theorem supportedRadicalRows_apply (a : U ≃L[ℝ] (K →L[ℝ] ℝ))
    (r : (ℝ × U) →L[ℝ] ℝ) (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U)))
    (v : ℝ × U) (k : K) : a (supportedRadicalRows a r Q v) k = r (Q k v) := by
  simp [supportedRadicalRows]

/-- The actual recovered coordinate of the radical representative with first coordinate one.
Source: `prop:supported-rank`, affine common-radical chart. -/
def supportedRadicalCoordinate (a : U ≃L[ℝ] (K →L[ℝ] ℝ))
    (r : (ℝ × U) →L[ℝ] ℝ) (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) : U :=
  supportedKernelBlockGraph (supportedRadicalRows a r Q) 1

/-- The actual affine representative, which is always nonzero by its first coordinate.
Source: `prop:supported-rank`, local common-radical recovery. -/
def supportedRadicalVector (a : U ≃L[ℝ] (K →L[ℝ] ℝ))
    (r : (ℝ × U) →L[ℝ] ℝ) (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) : ℝ × U :=
  (1, supportedRadicalCoordinate a r Q)

/-- The full actual vector residual at the recovered representative.
Source: `prop:supported-rank`, local equations for common-radical incidence. -/
def supportedRadicalResidual (a : U ≃L[ℝ] (K →L[ℝ] ℝ))
    (r : (ℝ × U) →L[ℝ] ℝ) (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) :
    K →L[ℝ] (ℝ × U) := Q.flip (supportedRadicalVector a r Q)

/-- Vanishing of the actual residual is equivalent to existence of a nonzero common radical
when the actual scalar right block is invertible. Proof: any common radical solves the scalar
row equation, hence lies in its actual one-dimensional graph. Its first coordinate cannot be
zero, so division by that coordinate recovers the chosen representative.
Source: `prop:supported-rank`, exact local zero-locus equivalence. -/
theorem supportedRadicalResidual_eq_zero_iff (a : U ≃L[ℝ] (K →L[ℝ] ℝ))
    (r : (ℝ × U) →L[ℝ] ℝ) (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U)))
    (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U)) :
    supportedRadicalResidual a r Q = 0 ↔
      ∃ v : ℝ × U, v ≠ 0 ∧ ∀ k : K, Q k v = 0 := by
  constructor
  · intro hz
    refine ⟨supportedRadicalVector a r Q, ?_, ?_⟩
    · intro hv
      have h := congrArg Prod.fst hv
      norm_num [supportedRadicalVector] at h
    · intro k
      have h := congrArg (fun L : K →L[ℝ] (ℝ × U) ↦ L k) hz
      simpa [supportedRadicalResidual] using h
  · rintro ⟨⟨t, u⟩, hne, hk⟩
    have hrow : supportedRadicalRows a r Q (t, u) = 0 := by
      apply a.injective
      ext k
      simp only [supportedRadicalRows_apply, hk, map_zero, zero_apply]
    have hgraph := (supportedKernel_mem_kernel_iff
      (supportedRadicalRows a r Q) e hA t u).mp hrow
    have ht : t ≠ 0 := by
      intro hzero
      apply hne
      simp [hzero] at hgraph
      exact Prod.ext hzero hgraph
    have hscale : supportedKernelBlockGraph (supportedRadicalRows a r Q) t =
        t • supportedRadicalCoordinate a r Q := by
      simpa [supportedRadicalCoordinate] using
        (supportedKernelBlockGraph (supportedRadicalRows a r Q)).map_smul t (1 : ℝ)
    have hv : (t, u) = t • supportedRadicalVector a r Q := by
      apply Prod.ext
      · simp [supportedRadicalVector]
      · simpa [supportedRadicalVector] using hgraph.trans hscale
    apply ContinuousLinearMap.ext
    intro k
    change Q k (supportedRadicalVector a r Q) = 0
    have hzero := hk k
    rw [hv, map_smul] at hzero
    exact (smul_eq_zero.mp hzero).resolve_left ht

/-- The recovered affine radical coordinate is genuinely smooth at every invertible row block.
Source: `prop:supported-rank`, local smooth recovery. -/
theorem supportedRadicalCoordinate_contDiffAt [CompleteSpace U]
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U)) :
    ContDiffAt ℝ ∞ (supportedRadicalCoordinate a r) Q := by
  have hr : ContDiff ℝ ∞ (supportedRadicalRows a r) := by fun_prop
  have h := (supportedKernelBlockGraph_contDiffAt (supportedRadicalRows a r Q) e hA).comp Q
    hr.contDiffAt
  simpa [supportedRadicalCoordinate, Function.comp_def] using!
    h.clm_apply (contDiffAt_const (c := (1 : ℝ)))

/-- The full actual common-radical residual is genuinely locally smooth.
Source: `prop:supported-rank`, local defining equations before the normal-coordinate projection. -/
theorem supportedRadicalResidual_contDiffAt [CompleteSpace U]
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U)) :
    ContDiffAt ℝ ∞ (supportedRadicalResidual a r) Q := by
  have hc := supportedRadicalCoordinate_contDiffAt a r Q e hA
  have hv := (contDiffAt_const (c := (1 : ℝ))).prodMk hc
  let flipMap : (K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) →L[ℝ]
      ((ℝ × U) →L[ℝ] (K →L[ℝ] (ℝ × U))) :=
    (ContinuousLinearMap.flipₗᵢ ℝ K (ℝ × U) (ℝ × U)).toContinuousLinearEquiv.toContinuousLinearMap
  have hf : ContDiff ℝ ∞ flipMap := by fun_prop
  simpa [supportedRadicalResidual, supportedRadicalVector] using! hf.contDiffAt.clm_apply hv

/-- The actual derivative of the full radical residual at the original radical line.
Proof: combine the actual kernel-block differential with evaluation at one, then differentiate
the original operator applied to the recovered affine vector. Both terms of the true product
rule are retained. Source: `prop:supported-rank`, local defining equations and tangent. -/
theorem supportedRadicalResidual_fderiv_apply [CompleteSpace U]
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r Q) = 0)
    (Δ : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (k : K) :
    (fderiv ℝ (supportedRadicalResidual a r) Q Δ) k =
      Δ k (1, 0) + Q k (0, -e.symm (supportedRadicalRows a r Δ (1, 0))) := by
  have hrows : HasFDerivAt (supportedRadicalRows a r) (supportedRadicalRows a r) Q := by
    simpa using! (supportedRadicalRows a r).hasFDerivAt (x := Q)
  have hg := (supportedKernelBlockGraph_hasFDerivAt
    (supportedRadicalRows a r Q) e hA hC).comp Q hrows
  have hc := hg.clm_apply (hasFDerivAt_const (x := Q) (c := (1 : ℝ)))
  have hv := (hasFDerivAt_const (x := Q) (c := (1 : ℝ))).prodMk hc
  let flipMap : (K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) →L[ℝ]
      ((ℝ × U) →L[ℝ] (K →L[ℝ] (ℝ × U))) :=
    (ContinuousLinearMap.flipₗᵢ ℝ K (ℝ × U) (ℝ × U)).toContinuousLinearEquiv.toContinuousLinearMap
  have hr := flipMap.hasFDerivAt.clm_apply hv
  have hbase : supportedKernelBlockGraph (supportedRadicalRows a r Q) = 0 := by
    simp [supportedKernelBlockGraph, hC]
  change HasFDerivAt (supportedRadicalResidual a r) _ Q at hr
  rw [hr.fderiv]
  simp [flipMap, hbase, supportedKernelLeftBlock, add_comm]

end GlobalEmbedding.Paper
