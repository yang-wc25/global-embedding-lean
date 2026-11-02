import Probes.Round4PrescribedNativeObservation

/-!
# The genuine four-phase zero coefficient of complete global amplitudes

All amplitudes are observed through the same real spatial map. Their native
source derivatives, complex derivative coefficients, and original zero-germ
selector are identified. Cross terms vanish from actual phase derivatives and
actual relative support. Neither a mean oracle nor a coefficient-support oracle
is supplied.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Filter
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GlobalEmbedding.Continuation
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

def round4ObservedCoefficient
    (phi : Fin r → Ep × M → ℝ) (tau : ℝ) (R Q : Fin r → Ep × M → V)
    (b : Ep) (obs : D → M) (x : D) (l : Fin r) (i : Fin (m+1)) (co : Fin N) : ℂ :=
  incrementsPrimaryDerivativeCoefficient (fun y => phi l (b,obs y)) tau
    (fun (_ : Unit) _ => 1) (fun _ y => R l (b,obs y)) (fun _ y => Q l (b,obs y))
    x (EuclideanSpace.single i 1) co

/-- The original four actual phase germs, including the physical scale tau. -/
def round4ObservedZeroMean
    (phi : Fin r → Ep × M → ℝ) (tau : ℝ) (R Q : Fin r → Ep × M → V)
    (b : Ep) (obs : D → M) (x : D) (i j : Fin (m+1)) : ℂ :=
  ∑ l, ∑ k, incrementsFourPhaseZeroGermPair (fun l y => phi l (b,obs y)/tau)
    (round4ObservedCoefficient phi tau R Q b obs x) x l k i j

/-- Identification of the opposite contribution with the same native tensor. -/
theorem round4_observed_opposite_native_mean
    (phi : Fin r → Ep × M → ℝ) (tau : ℝ) (R Q : Fin r → Ep × M → V)
    (b : Ep) (obs : D → M) (x : D) (i j : Fin (m+1))
    (hp : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phi l) (b,obs x))
    (hR : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ (R l) (b,obs x))
    (hQ : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ (Q l) (b,obs x))
    (hobs : ContMDiffAt 𝓘(ℝ,D) I ∞ obs x) :
    let w := fun k : Fin (m+1) => mfderiv 𝓘(ℝ,D) I obs x
      ((tangentSpaceCastModel 𝓘(ℝ,D) x).symm (EuclideanSpace.single k 1))
    (incrementsOppositePrimaryContribution (round4ObservedCoefficient phi tau R Q b obs x) i j).re =
      round4NativeOppositeMean (I:=I) phi tau R Q b (obs x) (w i) (w j) := by
  intro w
  let coeff := round4ObservedCoefficient phi tau R Q b obs x
  have hc (l : Fin r) (k : Fin (m+1)) (co : Fin N) : coeff l k co =
      (round4PrescribedNativeCoefficient (I:=I) false (phi l) tau (R l) (Q l) (b,obs x) (w k) co : ℂ) +
      Complex.I * (round4PrescribedNativeCoefficient (I:=I) true (phi l) tau (R l) (Q l) (b,obs x) (w k) co : ℂ) :=
    round4_native_observed_coefficient (phi l) (R l) (Q l) tau b obs x
      (EuclideanSpace.single k 1) co (hp l) (hR l) (hQ l) hobs
  have ht (l : Fin r) : ((1/4 : ℂ)*
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
  simp only [round4NativeOppositeMean,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.add_apply,LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,
    innerₗ_apply_apply,smul_eq_mul,Finset.mul_sum]

/-- Actual support and phase separation remove every nonopposite term. -/
theorem round4_observed_zero_native_mean
    (phi : Fin r → Ep × M → ℝ) (tau : ℝ) (R Q : Fin r → Ep × M → V)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hRsupport : ∀ l, tsupport (fun z : W => R l z) ⊆ Subtype.val ⁻¹' K l)
    (hQsupport : ∀ l, tsupport (fun z : W => Q l z) ⊆ Subtype.val ⁻¹' K l)
    (b : Ep) (obs : D → M) (x : D) (hxW : (b,obs x) ∈ W) (htau : tau ≠ 0)
    (hp : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phi l) (b,obs x))
    (hR : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ (R l) (b,obs x))
    (hQ : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ (Q l) (b,obs x))
    (hobs : ContMDiffAt 𝓘(ℝ,D) I ∞ obs x)
    (hdouble : ∀ l, (b,obs x) ∈ K l →
      fderiv ℝ (fun y => phi l (b,obs y)+phi l (b,obs y)) x ≠ 0)
    (hinteraction : ∀ l k, l ≠ k → (b,obs x) ∈ K l → (b,obs x) ∈ K k →
      fderiv ℝ (fun y => phi l (b,obs y)+phi k (b,obs y)) x ≠ 0 ∧
      fderiv ℝ (fun y => phi l (b,obs y)-phi k (b,obs y)) x ≠ 0)
    (i j : Fin (m+1)) :
    let w := fun k : Fin (m+1) => mfderiv 𝓘(ℝ,D) I obs x
      ((tangentSpaceCastModel 𝓘(ℝ,D) x).symm (EuclideanSpace.single k 1))
    (round4ObservedZeroMean phi tau R Q b obs x i j).re =
      round4NativeOppositeMean (I:=I) phi tau R Q b (obs x) (w i) (w j) := by
  intro w
  let ph := fun l y => phi l (b,obs y)
  let coeff := round4ObservedCoefficient phi tau R Q b obs x
  have hzero (f : Ep × M → V) (l : Fin r)
      (hs : tsupport (fun z : W => f z) ⊆ Subtype.val ⁻¹' K l)
      (hn : (b,obs x) ∉ K l) : (fun y => f (b,obs y)) =ᶠ[𝓝 x] 0 := by
    have hr : tsupport (fun z : W => f z) = Subtype.val ⁻¹' tsupport f := by
      change closure (Subtype.val ⁻¹' Function.support f : Set W) =
        Subtype.val ⁻¹' closure (Function.support f)
      exact (hW.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
        continuous_subtype_val (Function.support f)).symm
    have hh : f =ᶠ[𝓝 (b,obs x)] 0 := by
      apply notMem_tsupport_iff_eventuallyEq.mp
      intro hz
      apply hn
      apply hs (a := (⟨(b,obs x), hxW⟩ : W))
      rw [hr]
      exact hz
    exact hh.comp_tendsto (continuousAt_const.prodMk hobs.continuousAt).tendsto
  have hinactive (l : Fin r) (hn : (b,obs x) ∉ K l) (k : Fin (m+1)) : coeff l k = 0 := by
    have hr := hzero (R l) l (hRsupport l) hn
    have hq := hzero (Q l) l (hQsupport l) hn
    funext co
    simp only [coeff,round4ObservedCoefficient,incrementsPrimaryDerivativeCoefficient]
    rw [hr.fderiv_eq (𝕜:=ℝ),hq.fderiv_eq (𝕜:=ℝ),hr.eq_of_nhds,hq.eq_of_nhds]
    simp
  have hz : round4ObservedZeroMean phi tau R Q b obs x i j =
      incrementsOppositePrimaryContribution coeff i j := by
    unfold round4ObservedZeroMean
    change (∑ l, ∑ k, incrementsFourPhaseZeroGermPair (fun l y => ph l y/tau) coeff x l k i j) = _
    simp_rw [increments_four_phase_zero_germ_pair_div ph tau htau]
    exact increments_four_phase_zero_germ_eq_opposite ph coeff
      (fun l => {y | (b,obs y) ∈ K l}) x hinactive hdouble hinteraction i j
  rw [hz]
  exact round4_observed_opposite_native_mean phi tau R Q b obs x i j hp hR hQ hobs

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_observed_opposite_native_mean
#print axioms GlobalEmbedding.Continuation.round4_observed_zero_native_mean
