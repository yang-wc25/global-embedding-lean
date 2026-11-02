import NormalPolar.ParameterDisplacementPrimaryGrouped
import Probes.ActualIncrementPrimaryObservationSum

/-! The actual spatial first-derivative identity on an original open observation
domain. Relative amplitude support gives the inactive zero germs; phase
regularity is required only on each original active neighborhood. -/

noncomputable section
open Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem actual_supported_primary_observed_grouped_derivative
    {m N : ℕ} {P Ep Label : Type*} [TopologicalSpace P]
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [Fintype Label]
    (phase : Label → P → ℝ) (tau : ℝ)
    (R Q : Label → P → EuclideanSpace ℝ (Fin N))
    (W : Set P) (hW : IsOpen W) (K : Label → Set P)
    (hRsupport : ∀ l, tsupport (fun z : W => R l z) ⊆ Subtype.val ⁻¹' K l)
    (hQsupport : ∀ l, tsupport (fun z : W => Q l z) ⊆ Subtype.val ⁻¹' K l)
    (kappa : Ep × EuclideanSpace ℝ (Fin (m+1)) → P)
    (Omega : Set (Ep × EuclideanSpace ℝ (Fin (m+1)))) (hOmega : IsOpen Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (O : Label → Set (Ep × EuclideanSpace ℝ (Fin (m+1))))
    (hO : ∀ l, IsOpen (O l)) (hcover : ∀ l, Omega ∩ kappa ⁻¹' K l ⊆ O l)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l ∘ kappa) (O l))
    (hR : ∀ l, ContDiffOn ℝ ∞ (R l ∘ kappa) Omega)
    (hQ : ∀ l, ContDiffOn ℝ ∞ (Q l ∘ kappa) Omega)
    (z : Ep × EuclideanSpace ℝ (Fin (m+1))) (hz : z ∈ Omega) (i : Fin (m+1)) :
    fderiv ℝ (fun x => ∑ l, (Real.cos (phase l (kappa (z.1,x))/tau) • R l (kappa (z.1,x)) -
      Real.sin (phase l (kappa (z.1,x))/tau) • Q l (kappa (z.1,x)))) z.2 (EuclideanSpace.single i 1) =
    incrementsGroupedRealDerivative (fun l => phase l (kappa z)/tau)
      (incrementsSecondaryPhysicalCoefficient (fun l b x => phase l (kappa (b,x))) tau
        (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
        (fun l b (_ : Unit) x => R l (kappa (b,x)))
        (fun l b (_ : Unit) x => Q l (kappa (b,x)))
        (fun k _ => EuclideanSpace.single k 1) z) i := by
  let incl := fun x : EuclideanSpace ℝ (Fin (m+1)) => (z.1,x)
  have hi : ContDiff ℝ ∞ incl := contDiff_const.prodMk contDiff_id
  have hRdiff (l : Label) : DifferentiableAt ℝ (fun x => R l (kappa (z.1,x))) z.2 := by
    exact (((hR l).contDiffAt (hOmega.mem_nhds hz)).comp z.2 hi.contDiffAt).differentiableAt (by simp)
  have hQdiff (l : Label) : DifferentiableAt ℝ (fun x => Q l (kappa (z.1,x))) z.2 := by
    exact (((hQ l).contDiffAt (hOmega.mem_nhds hz)).comp z.2 hi.contDiffAt).differentiableAt (by simp)
  have hpdiff (l : Label) (hl : kappa z ∈ K l) :
      DifferentiableAt ℝ (fun x => phase l (kappa (z.1,x))) z.2 := by
    exact (((hphase l).contDiffAt ((hO l).mem_nhds (hcover l ⟨hz,hl⟩))).comp
      z.2 hi.contDiffAt).differentiableAt (by simp)
  have hRzero (l : Label) (hl : kappa z ∉ K l) :
      (fun x => R l (kappa (z.1,x))) =ᶠ[𝓝 z.2] 0 := by
    have hh := parameterRound2_relative_observation_zero_germ (R l) W (K l) hW (hRsupport l)
      kappa z (hkappa.continuousAt (hOmega.mem_nhds hz)) (hmap hz) hl
    exact hh.comp_tendsto hi.continuous.continuousAt.tendsto
  have hQzero (l : Label) (hl : kappa z ∉ K l) :
      (fun x => Q l (kappa (z.1,x))) =ᶠ[𝓝 z.2] 0 := by
    have hh := parameterRound2_relative_observation_zero_germ (Q l) W (K l) hW (hQsupport l)
      kappa z (hkappa.continuousAt (hOmega.mem_nhds hz)) (hmap hz) hl
    exact hh.comp_tendsto hi.continuous.continuousAt.tendsto
  exact actual_supported_primary_grouped_derivative
    (fun l x => phase l (kappa (z.1,x))) tau
    (fun l x => R l (kappa (z.1,x))) (fun l x => Q l (kappa (z.1,x)))
    (fun l => kappa z ∈ K l) z.2 hpdiff hRdiff hQdiff hRzero hQzero i

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_supported_primary_observed_grouped_derivative
