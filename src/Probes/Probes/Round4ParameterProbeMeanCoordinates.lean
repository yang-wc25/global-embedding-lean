import Probes.Round4ParameterProbeLocalMean
import Probes.Round4PrescribedNativeObservation
import Probes.ActualSecondaryTotalMetricCoordinates
import Probes.ActualSecondaryCompleteMetricIdentity

/-! Actual native opposite means in the unchanged original atlas. The finite
label type is kept, so the same background/probe Sum array and all its signed
secondary coefficients are used without relabeling or a coordinate oracle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GlobalEmbedding.Continuation
variable {E H M Ep Label : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [Fintype Label] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

def round4ParameterProbeArrayMean
    (phi : Label → Ep × M → ℝ) (tau : ℝ) (R Q : Label → Ep × M → V)
    (b : Ep) (x : M) : LinearMap.BilinForm ℝ (TangentSpace I x) :=
  (1/2 : ℝ) • ∑ l,
    (LinearMap.BilinForm.comp (innerₗ V)
      (round4PrescribedNativeCoefficient (I:=I) false (phi l) tau (R l) (Q l) (b,x)).toLinearMap
      (round4PrescribedNativeCoefficient (I:=I) false (phi l) tau (R l) (Q l) (b,x)).toLinearMap +
    LinearMap.BilinForm.comp (innerₗ V)
      (round4PrescribedNativeCoefficient (I:=I) true (phi l) tau (R l) (Q l) (b,x)).toLinearMap
      (round4PrescribedNativeCoefficient (I:=I) true (phi l) tau (R l) (Q l) (b,x)).toLinearMap)

def round4ParameterProbeArrayObservedCoefficient
    (phi : Label → Ep × M → ℝ) (tau : ℝ) (R Q : Label → Ep × M → V)
    (b : Ep) (obs : D → M) (x : D) (l : Label) (i : Fin (m+1)) (co : Fin N) : ℂ :=
  incrementsPrimaryDerivativeCoefficient (fun y => phi l (b,obs y)) tau
    (fun (_ : Unit) _ => 1) (fun _ y => R l (b,obs y)) (fun _ y => Q l (b,obs y))
    x (EuclideanSpace.single i 1) co

/-- Identification of the opposite contribution with the same native tensor. -/
theorem round4ParameterProbe_array_mean_observed
    (phi : Label → Ep × M → ℝ) (tau : ℝ) (R Q : Label → Ep × M → V)
    (b : Ep) (obs : D → M) (x : D) (i j : Fin (m+1))
    (hp : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phi l) (b,obs x))
    (hR : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ (R l) (b,obs x))
    (hQ : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ (Q l) (b,obs x))
    (hobs : ContMDiffAt 𝓘(ℝ,D) I ∞ obs x) :
    let w := fun k : Fin (m+1) => mfderiv 𝓘(ℝ,D) I obs x
      ((tangentSpaceCastModel 𝓘(ℝ,D) x).symm (EuclideanSpace.single k 1))
    (incrementsOppositePrimaryContribution (round4ParameterProbeArrayObservedCoefficient phi tau R Q b obs x) i j).re =
      round4ParameterProbeArrayMean (I:=I) phi tau R Q b (obs x) (w i) (w j) := by
  intro w
  let coeff := round4ParameterProbeArrayObservedCoefficient phi tau R Q b obs x
  have hc (l : Label) (k : Fin (m+1)) (co : Fin N) : coeff l k co =
      (round4PrescribedNativeCoefficient (I:=I) false (phi l) tau (R l) (Q l) (b,obs x) (w k) co : ℂ) +
      Complex.I * (round4PrescribedNativeCoefficient (I:=I) true (phi l) tau (R l) (Q l) (b,obs x) (w k) co : ℂ) :=
    round4_native_observed_coefficient (phi l) (R l) (Q l) tau b obs x
      (EuclideanSpace.single k 1) co (hp l) (hR l) (hQ l) hobs
  have ht (l : Label) : ((1/4 : ℂ)*
      ((coeff l i ⬝ᵥ (fun co => conj (coeff l j co))) +
        ((fun co => conj (coeff l i co)) ⬝ᵥ coeff l j))).re = (1/2 : ℝ)*
      (inner ℝ (round4PrescribedNativeCoefficient (I:=I) false (phi l) tau (R l) (Q l) (b,obs x) (w i))
        (round4PrescribedNativeCoefficient (I:=I) false (phi l) tau (R l) (Q l) (b,obs x) (w j)) +
      inner ℝ (round4PrescribedNativeCoefficient (I:=I) true (phi l) tau (R l) (Q l) (b,obs x) (w i))
        (round4PrescribedNativeCoefficient (I:=I) true (phi l) tau (R l) (Q l) (b,obs x) (w j))) := by
    rw [show (1/4 : ℂ) = ((1/4 : ℝ) : ℂ) by norm_num]
    simp only [dotProduct,hc,Complex.mul_re,Complex.add_re,Complex.mul_im,Complex.add_im,
      Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
      Complex.I_im,Complex.re_sum,Complex.im_sum,zero_mul,mul_zero,one_mul,zero_add,add_zero,
      sub_zero,PiLp.inner_apply,Real.inner_apply]
    ring_nf
    rw [Finset.sum_add_distrib]
    ring
  change (incrementsOppositePrimaryContribution coeff i j).re = _
  unfold incrementsOppositePrimaryContribution
  rw [Complex.re_sum]
  simp_rw [ht]
  simp only [round4ParameterProbeArrayMean,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.add_apply,LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,
    innerₗ_apply_apply,smul_eq_mul,Finset.mul_sum]


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_array_mean_observed

namespace GlobalEmbedding.Continuation
variable {m d N pcount : ℕ} {M Label : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

/-- The tensor used by the complete secondary metric identity is the genuine
native opposite mean in the original parameter/source observer. Both ordered
tensor slots and the actual source inverse derivative are retained. -/
theorem round4ParameterProbe_array_mean_original
    (atlas : BufferedAtlas M D) (param : Fin pcount → OpenPartialHomeomorph Ep Ep)
    (hAtlas : IsSmoothBufferedAtlas atlas)
    (phase : Label → Ep × M → ℝ) (tau : ℝ) (R Q : Label → Ep × M → V)
    (idx : Fin atlas.count × Fin pcount) (z : X)
    (hz : z.2 ∈ (atlas.chart idx.1).target)
    (hp : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (phase l)
      ((param idx.2).symm z.1,(atlas.chart idx.1).symm z.2))
    (hR : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (R l)
      ((param idx.2).symm z.1,(atlas.chart idx.1).symm z.2))
    (hQ : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Q l)
      ((param idx.2).symm z.1,(atlas.chart idx.1).symm z.2)) :
    actualOriginalNativeTargetTensor atlas param
      (round4ParameterProbeArrayMean (I:=𝓙) phase tau R Q) idx z =
    actualPrimaryOppositeMeanTensor
      (fun l t x => phase l ((param idx.2).symm t,(atlas.chart idx.1).symm x)) tau
      (fun (_ : Label) (_ : Ep) (_ : Unit) (_ : D) => 1)
      (fun l t (_ : Unit) x => R l ((param idx.2).symm t,(atlas.chart idx.1).symm x))
      (fun l t (_ : Unit) x => Q l ((param idx.2).symm t,(atlas.chart idx.1).symm x)) z := by
  have hobs : ContMDiffAt 𝓘(ℝ,D) 𝓙 ∞ (atlas.chart idx.1).symm z.2 :=
    (contMDiffOn_symm_of_mem_maximalAtlas (hAtlas.chart_mem idx.1)).contMDiffAt
      ((atlas.chart idx.1).open_target.mem_nhds hz)
  apply actual_bilinear_tensor_eq_of_basis
  intro i j
  simp only [actualOriginalNativeTargetTensor_basis,actualPrimaryOppositeMeanTensor,
    actualRealTensorAssembly_basis]
  exact (round4ParameterProbe_array_mean_observed phase tau R Q ((param idx.2).symm z.1)
    (atlas.chart idx.1).symm z.2 i j hp hR hQ hobs).symm

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_array_mean_original
