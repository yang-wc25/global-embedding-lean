import Probes.ActualSecondaryFiniteTensorIdentity
import GlobalEmbedding.Paper.IncrementsPrimaryWaveFirstJet

/-!
# The actual common primary derivative with carrier-local phases

Only active phases are differentiated. The inactive terms have zero amplitude
germs, so the literal wave and its genuine grouped coefficient both vanish
there. No regularity or replacement of the phase away from its carrier is
required in the result.
-/

noncomputable section
open Set Filter Function GlobalEmbedding.Paper
open scoped Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem actual_supported_primary_grouped_derivative
    {n N : ℕ} {Label : Type*} [Fintype Label]
    (phase : Label → EuclideanSpace ℝ (Fin n) → ℝ) (tau : ℝ)
    (R Q : Label → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (active : Label → Prop) (x : EuclideanSpace ℝ (Fin n))
    (hphase : ∀ l, active l → DifferentiableAt ℝ (phase l) x)
    (hR : ∀ l, DifferentiableAt ℝ (R l) x)
    (hQ : ∀ l, DifferentiableAt ℝ (Q l) x)
    (hRzero : ∀ l, ¬active l → R l =ᶠ[𝓝 x] 0)
    (hQzero : ∀ l, ¬active l → Q l =ᶠ[𝓝 x] 0)
    (i : Fin n) :
    fderiv ℝ (fun y => ∑ l, (Real.cos (phase l y/tau) • R l y -
      Real.sin (phase l y/tau) • Q l y)) x (EuclideanSpace.single i 1) =
    incrementsGroupedRealDerivative (fun l => phase l x/tau)
      (fun l k => incrementsPrimaryDerivativeCoefficient (phase l) tau
        (fun (_ : Unit) _ => 1) (fun _ => R l) (fun _ => Q l) x
        (EuclideanSpace.single k 1)) i := by
  let coeff := fun l k => incrementsPrimaryDerivativeCoefficient (phase l) tau
    (fun (_ : Unit) _ => 1) (fun _ => R l) (fun _ => Q l) x
    (EuclideanSpace.single k 1)
  let activePhase := fun l y => if active l then phase l y else 0
  have hp (l : Label) : DifferentiableAt ℝ (activePhase l) x := by
    by_cases hl : active l
    · simpa only [activePhase,hl,ite_true] using hphase l hl
    · simpa only [activePhase,hl,ite_false] using differentiableAt_const (0 : ℝ)
  have hformula (theta : Label → EuclideanSpace ℝ (Fin n) → ℝ) :
      incrementsPrimaryWave theta tau (fun _ (_ : Unit) _ => 1)
        (fun l _ => R l) (fun l _ => Q l) =
      fun y => ∑ l, (Real.cos (theta l y/tau) • R l y -
        Real.sin (theta l y/tau) • Q l y) := by
    funext y
    unfold incrementsPrimaryWave
    simp only [Finset.univ_unique,Finset.sum_singleton,one_smul]
    apply Finset.sum_congr rfl
    intro l _
    exact congrFun (increments_primary_real_mode_eq (theta l) tau (R l) (Q l)) y
  have hsame : (fun y => ∑ l, (Real.cos (phase l y/tau) • R l y -
      Real.sin (phase l y/tau) • Q l y)) =ᶠ[𝓝 x]
      incrementsPrimaryWave activePhase tau (fun _ (_ : Unit) _ => 1)
        (fun l _ => R l) (fun l _ => Q l) := by
    rw [hformula]
    have hterm (l : Label) :
        (fun y => Real.cos (phase l y/tau) • R l y - Real.sin (phase l y/tau) • Q l y) =ᶠ[𝓝 x]
        (fun y => Real.cos (activePhase l y/tau) • R l y - Real.sin (activePhase l y/tau) • Q l y) := by
      by_cases hl : active l
      · simp only [activePhase,hl,ite_true]
        exact Filter.EventuallyEq.rfl
      · filter_upwards [hRzero l hl,hQzero l hl] with y hRy hQy
        simp only [hRy,hQy,Pi.zero_apply,smul_zero,sub_zero]
    filter_upwards [eventually_all.mpr hterm] with y hy
    exact Finset.sum_congr rfl (fun l _ => hy l)
  have hcoeff : (fun l k => incrementsPrimaryDerivativeCoefficient (activePhase l) tau
      (fun (_ : Unit) _ => 1) (fun _ => R l) (fun _ => Q l) x
      (EuclideanSpace.single k 1)) = coeff := by
    funext l k co
    by_cases hl : active l
    · simp only [activePhase,hl,ite_true,coeff]
    · have hRv : R l x = 0 := (hRzero l hl).eq_of_nhds
      have hQv : Q l x = 0 := (hQzero l hl).eq_of_nhds
      simp only [coeff,incrementsPrimaryDerivativeCoefficient,hRv,hQv,
        WithLp.ofLp_zero,Pi.zero_apply,Complex.ofReal_zero,mul_zero,zero_add,add_zero]
  have hinactive (l : Label) (hl : ¬active l) (k : Fin n) (co : Fin N) : coeff l k co = 0 := by
    have hRv : R l x = 0 := (hRzero l hl).eq_of_nhds
    have hQv : Q l x = 0 := (hQzero l hl).eq_of_nhds
    have hRd : fderiv ℝ (R l) x = 0 := by
      rw [(hRzero l hl).fderiv_eq (𝕜 := ℝ)]
      exact fderiv_const_apply (0 : EuclideanSpace ℝ (Fin N))
    have hQd : fderiv ℝ (Q l) x = 0 := by
      rw [(hQzero l hl).fderiv_eq (𝕜 := ℝ)]
      exact fderiv_const_apply (0 : EuclideanSpace ℝ (Fin N))
    simp only [coeff,incrementsPrimaryDerivativeCoefficient,hRv,hQv,hRd,hQd,
      ContinuousLinearMap.zero_apply,WithLp.ofLp_zero,Pi.zero_apply,Complex.ofReal_zero,
      mul_zero,zero_add,add_zero,Finset.sum_const_zero]
  have hgroup : incrementsGroupedRealDerivative (fun l => activePhase l x/tau) coeff i =
      incrementsGroupedRealDerivative (fun l => phase l x/tau) coeff i := by
    ext co
    change (∑ l, (incrementsMeanPhase (activePhase l x/tau)*coeff l i co).re) =
      ∑ l, (incrementsMeanPhase (phase l x/tau)*coeff l i co).re
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : active l
    · simp only [activePhase,hl,ite_true]
    · simp only [hinactive l hl,mul_zero]
  have hh := increments_primary_wave_grouped_derivative activePhase tau
    (fun _ (_ : Unit) _ => 1) (fun l _ => R l) (fun l _ => Q l) x
    (EuclideanSpace.single i 1) hp (fun _ _ => differentiableAt_const 1)
    (fun l _ => hR l) (fun l _ => hQ l)
  change fderiv ℝ _ x (EuclideanSpace.single i 1) =
    incrementsGroupedRealDerivative (fun l => activePhase l x/tau)
      (fun l k => incrementsPrimaryDerivativeCoefficient (activePhase l) tau
        (fun (_ : Unit) _ => 1) (fun _ => R l) (fun _ => Q l) x
        (EuclideanSpace.single k 1)) i at hh
  rw [hcoeff,hgroup] at hh
  rw [hsame.fderiv_eq (𝕜 := ℝ)]
  exact hh

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_supported_primary_grouped_derivative
