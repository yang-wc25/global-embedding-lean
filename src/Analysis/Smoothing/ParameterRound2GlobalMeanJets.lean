import Smoothing.ParameterRound2GlobalMeanIdentity

/-! The SAME global observed mean, with true primary local multiplicity.
All subordinate pieces have already been transported and grouped by phase
inside GlobalObservedError. Unit polarization retains every same-phase
cross term. Genuine inactive germs remove the inactive primary terms.
The size and difference constants contain no total primary/chart count. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_actual_globalMean_coefficient_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length j Lprimary : ℕ) (i i' : Fin (m+1))
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hsupport : ∀ ν β, incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ (g.chart ν β).source)
    (hinverse : ∀ ν β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2))
    (e : OpenPartialHomeomorph M D) (Omega S : Set X) (U : Λ → Set X)
    (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn (fun z : X => (z.1,e.symm z.2)) Omega)
    (hmap : MapsTo (fun z : X => (z.1,e.symm z.2)) Omega W)
    (hU : ∀ ν, IsOpen (U ν))
    (hOU : ∀ ν, Omega ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff ν) ⊆ U ν)
    (hCount : ∀ z ∈ S, (Finset.univ.filter (fun ν => (z.1,e.symm z.2) ∈
      incrementsGlobalRelativeSupport W (g.cutoff ν))).card ≤ Lprimary)
    (ell tau Mcoef Delta : ℝ) (hell : 0 < ell) (htau : 0 < tau)
    (htaul : tau ≤ ell) (hMcoef : 0 ≤ Mcoef) (hDelta : 0 ≤ Delta) :
    let LA := fun ν (z : X) => incrementsGlobalObservedLeading F g input e z.1 z.2 ν
    let LB := fun ν (z : X) => incrementsGlobalObservedLeading F g inputbar e z.1 z.2 ν
    let EA := fun ν (z : X) => incrementsGlobalObservedError F hF g input length tau e z.1 z.2 ν
    let EB := fun ν (z : X) => incrementsGlobalObservedError F hF g inputbar length tau e z.1 z.2 ν
    (∀ ν, ContDiffOn ℝ ∞ (LA ν) (U ν)) →
    (∀ ν, ContDiffOn ℝ ∞ (LB ν) (U ν)) →
    (∀ ν, ContDiffOn ℝ ∞ (EA ν) (U ν)) →
    (∀ ν, ContDiffOn ℝ ∞ (EB ν) (U ν)) →
    (∀ ν k, k ≤ j → ∀ z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff ν),
      ell^k * ‖iteratedFDeriv ℝ k (LA ν) z‖ ≤ Mcoef) →
    (∀ ν k, k ≤ j → ∀ z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff ν),
      ell^k * ‖iteratedFDeriv ℝ k (LB ν) z‖ ≤ Mcoef) →
    (∀ ν k, k ≤ j → ∀ z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff ν),
      ell^k * ‖iteratedFDeriv ℝ k (EA ν) z‖ ≤ Mcoef*(tau/ell)) →
    (∀ ν k, k ≤ j → ∀ z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff ν),
      ell^k * ‖iteratedFDeriv ℝ k (EB ν) z‖ ≤ Mcoef*(tau/ell)) →
    (∀ ν k, k ≤ j → ∀ z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff ν),
      ell^k * ‖iteratedFDeriv ℝ k (fun w => LA ν w-LB ν w) z‖ ≤ Mcoef*Delta) →
    (∀ ν k, k ≤ j → ∀ z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff ν),
      ell^k * ‖iteratedFDeriv ℝ k (fun w => EA ν w-EB ν w) z‖ ≤ Mcoef*(tau/ell)*Delta) →
    let C := (Lprimary:ℝ)*(6*‖incrementsMeanBilinear (Λ := Unit) (N := N) i i'‖*2^j*Mcoef^2)
    let meanA := fun z => parameterRound2_globalObservedMeanCoefficient F hF g input length tau e z i i'
    let meanB := fun z => parameterRound2_globalObservedMeanCoefficient F hF g inputbar length tau e z i i'
    (ContDiffOn ℝ ∞ meanA Omega ∧ ContDiffOn ℝ ∞ meanB Omega) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k meanA z‖ ≤ C*(tau/ell)) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k meanB z‖ ≤ C*(tau/ell)) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => meanA w-meanB w) z‖ ≤ C*(tau/ell)*Delta) := by
  intro LA LB EA EB hLA hLB hEA hEB hLAb hLBb hEAb hEBb hLd hEd C meanA meanB
  let epsilon := tau/ell
  have heps : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have heps1 : epsilon ≤ 1 := (div_le_one hell).2 htaul
  let K := 6*‖incrementsMeanBilinear (Λ := Unit) (N := N) i i'‖*2^j*Mcoef^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let fA := fun ν (z : X) => incrementsMeanRemainder (fun _ : Unit => LA ν z) (fun _ : Unit => EA ν z) i i'
  let fB := fun ν (z : X) => incrementsMeanRemainder (fun _ : Unit => LB ν z) (fun _ : Unit => EB ν z) i i'
  have hfa (ν) : ContDiffOn ℝ ∞ (fA ν) (U ν) :=
    incrementsMeanRemainder_contDiffOn (U ν) _ _ (contDiffOn_pi.2 (fun _ => hLA ν))
      (contDiffOn_pi.2 (fun _ => hEA ν)) i i'
  have hfb (ν) : ContDiffOn ℝ ∞ (fB ν) (U ν) :=
    incrementsMeanRemainder_contDiffOn (U ν) _ _ (contDiffOn_pi.2 (fun _ => hLB ν))
      (contDiffOn_pi.2 (fun _ => hEB ν)) i i'
  have hzeroA (ν) (z) (hz : z ∈ Omega)
      (hn : (z.1,e.symm z.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff ν)) :
      fA ν =ᶠ[𝓝 z] (fun _ => 0) := by
    have hz0 := (parameterRound2_actual_globalObserved_inactive_germ F hF g input length tau
      W hW ν (hsupport ν) (hinverse ν) e Omega hOmega hkappa hmap z hz hn).2
    filter_upwards [hz0] with w hw
    simp only [fA,EA,hw,incrementsMeanRemainder]
    change incrementsMeanRemainder (fun _ : Unit => LA ν w) 0 i i' = 0
    simp [incrementsMeanRemainder]
  have hzeroB (ν) (z) (hz : z ∈ Omega)
      (hn : (z.1,e.symm z.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff ν)) :
      fB ν =ᶠ[𝓝 z] (fun _ => 0) := by
    have hz0 := (parameterRound2_actual_globalObserved_inactive_germ F hF g inputbar length tau
      W hW ν (hsupport ν) (hinverse ν) e Omega hOmega hkappa hmap z hz hn).2
    filter_upwards [hz0] with w hw
    simp only [fB,EB,hw,incrementsMeanRemainder]
    change incrementsMeanRemainder (fun _ : Unit => LB ν w) 0 i i' = 0
    simp [incrementsMeanRemainder]
  have unitJet (ν) (f : X → Fin (m+1) → Fin N → ℂ) (hf : ContDiffOn ℝ ∞ f (U ν))
      (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (z : X)
      (hz : z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
        incrementsGlobalRelativeSupport W (g.cutoff ν))
      (hb : ell^k*‖iteratedFDeriv ℝ k f z‖ ≤ R) :
      ell^k*‖iteratedFDeriv ℝ k (fun w (_ : Unit) => f w) z‖ ≤ R := by
    exact parameterRound2_joint_pi_weighted_jet _ z
      ((contDiffOn_pi.2 (fun _ => hf)).contDiffAt ((hU ν).mem_nhds (hOU ν ⟨hSOmega hz.1,hz.2⟩)))
      k ell R hell hR (fun _ => hb)
  have hper (ν) :
      (∀ k ≤ j, ∀ z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
        incrementsGlobalRelativeSupport W (g.cutoff ν), ell^k*‖iteratedFDeriv ℝ k (fA ν) z‖ ≤ K*epsilon) ∧
      (∀ k ≤ j, ∀ z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
        incrementsGlobalRelativeSupport W (g.cutoff ν), ell^k*‖iteratedFDeriv ℝ k (fB ν) z‖ ≤ K*epsilon) ∧
      (∀ k ≤ j, ∀ z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
        incrementsGlobalRelativeSupport W (g.cutoff ν),
        ell^k*‖iteratedFDeriv ℝ k (fun w => fA ν w-fB ν w) z‖ ≤ K*epsilon*Delta) := by
    have hA1 := contDiffOn_pi.2 (fun _ : Unit => hLA ν)
    have hB1 := contDiffOn_pi.2 (fun _ : Unit => hLB ν)
    have hA2 := contDiffOn_pi.2 (fun _ : Unit => hEA ν)
    have hB2 := contDiffOn_pi.2 (fun _ : Unit => hEB ν)
    refine ⟨?_,?_,?_⟩
    · intro k hk z hz
      have hh := incrementsMeanRemainder_scaled_jet (U ν) (hU ν) _ _ hA1 hA2 i i' k ell
        Mcoef epsilon hell.le hMcoef heps heps1 (hOU ν ⟨hSOmega hz.1,hz.2⟩)
        (fun r hr => unitJet ν _ (hLA ν) _ hMcoef r z hz (hLAb ν r (hr.trans hk) z hz))
        (fun r hr => unitJet ν _ (hEA ν) _ (mul_nonneg hMcoef heps) r z hz (hEAb ν r (hr.trans hk) z hz))
      apply hh.trans
      dsimp only [K]
      gcongr <;> norm_num
    · intro k hk z hz
      have hh := incrementsMeanRemainder_scaled_jet (U ν) (hU ν) _ _ hB1 hB2 i i' k ell
        Mcoef epsilon hell.le hMcoef heps heps1 (hOU ν ⟨hSOmega hz.1,hz.2⟩)
        (fun r hr => unitJet ν _ (hLB ν) _ hMcoef r z hz (hLBb ν r (hr.trans hk) z hz))
        (fun r hr => unitJet ν _ (hEB ν) _ (mul_nonneg hMcoef heps) r z hz (hEBb ν r (hr.trans hk) z hz))
      apply hh.trans
      dsimp only [K]
      gcongr <;> norm_num
    · intro k hk z hz
      have hh := incrementsMeanRemainder_difference_scaled_jet (U ν) (hU ν) _ _ _ _
        hA1 hA2 hB1 hB2 i i' k ell Mcoef epsilon Delta hell.le hMcoef heps heps1 hDelta
        (hOU ν ⟨hSOmega hz.1,hz.2⟩)
        (fun r hr => unitJet ν _ (hLA ν) _ hMcoef r z hz (hLAb ν r (hr.trans hk) z hz))
        (fun r hr => unitJet ν _ (hEB ν) _ (mul_nonneg hMcoef heps) r z hz (hEBb ν r (hr.trans hk) z hz))
        (fun r hr => unitJet ν _ (hLB ν) _ hMcoef r z hz (hLBb ν r (hr.trans hk) z hz))
        (fun r hr => unitJet ν _ (hEA ν) _ (mul_nonneg hMcoef heps) r z hz (hEAb ν r (hr.trans hk) z hz))
        (fun r hr => unitJet ν _ ((hLA ν).sub (hLB ν)) _ (mul_nonneg hMcoef hDelta) r z hz (hLd ν r (hr.trans hk) z hz))
        (fun r hr => unitJet ν _ ((hEA ν).sub (hEB ν)) _ (mul_nonneg (mul_nonneg hMcoef heps) hDelta)
          r z hz (hEd ν r (hr.trans hk) z hz))
      apply hh.trans
      dsimp only [K]
      gcongr; norm_num
  have sumBound (f : Λ → X → ℂ) (hf : ∀ ν, ContDiffOn ℝ ∞ (f ν) (U ν))
      (hzero : ∀ ν z, z ∈ Omega → (z.1,e.symm z.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff ν) →
        f ν =ᶠ[𝓝 z] (fun _ => 0)) (R : ℝ) (hR : 0 ≤ R)
      (hb : ∀ ν k, k ≤ j → ∀ z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
        incrementsGlobalRelativeSupport W (g.cutoff ν), ell^k*‖iteratedFDeriv ℝ k (f ν) z‖ ≤ R) :
      ContDiffOn ℝ ∞ (fun z => ∑ ν, f ν z) Omega ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => ∑ ν, f ν w) z‖ ≤ (Lprimary:ℝ)*R := by
    have hfull (ν) : ContDiffOn ℝ ∞ (f ν) Omega := by
      intro z hz
      by_cases hm : (z.1,e.symm z.2) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν)
      · exact ((hf ν).contDiffAt ((hU ν).mem_nhds (hOU ν ⟨hz,hm⟩))).contDiffWithinAt
      · exact (contDiffAt_const.congr_of_eventuallyEq (hzero ν z hz hm)).contDiffWithinAt
    refine ⟨ContDiffOn.sum (fun ν _ => hfull ν),?_⟩
    intro k hk z hz
    let active := Finset.univ.filter (fun ν => (z.1,e.symm z.2) ∈ incrementsGlobalRelativeSupport W (g.cutoff ν))
    have hh := parameter_finite_sum_jet_le f z active Lprimary k (R/ell^k) (hCount z hz) (by positivity)
      (fun ν _ => (hfull ν).contDiffAt (hOmega.mem_nhds (hSOmega hz)))
      (by
        intro ν hn
        apply hzero ν z (hSOmega hz)
        intro hm
        exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩))
      (by
        intro ν hn
        apply (le_div_iff₀ (pow_pos hell k)).2
        simpa only [mul_comm] using hb ν k hk z ⟨hz,(Finset.mem_filter.mp hn).2⟩)
    calc
      _ ≤ ell^k*((Lprimary:ℝ)*(R/ell^k)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hell.le k)
      _ = _ := by field_simp [(pow_pos hell k).ne']
  have ha := sumBound fA hfa hzeroA (K*epsilon) (mul_nonneg hK heps) (fun ν => (hper ν).1)
  have hb := sumBound fB hfb hzeroB (K*epsilon) (mul_nonneg hK heps) (fun ν => (hper ν).2.1)
  have hd := sumBound (fun ν z => fA ν z-fB ν z) (fun ν => (hfa ν).sub (hfb ν))
    (by
      intro ν z hz hn
      filter_upwards [hzeroA ν z hz hn,hzeroB ν z hz hn] with w hwA hwB
      simp only [hwA,hwB,sub_self])
    (K*epsilon*Delta) (mul_nonneg (mul_nonneg hK heps) hDelta) (fun ν => (hper ν).2.2)
  have heq : (fun z => ∑ ν, (fA ν z-fB ν z)) = fun z => meanA z-meanB z := by
    funext z
    simp only [meanA,meanB,parameterRound2_globalObservedMeanCoefficient,
      fA,fB,LA,LB,EA,EB,Finset.sum_sub_distrib]
  rw [heq] at hd
  refine ⟨⟨ha.1,hb.1⟩,?_,?_,?_⟩
  · intro k hk z hz
    exact (ha.2 k hk z hz).trans_eq (by dsimp only [C,K,epsilon]; ring)
  · intro k hk z hz
    exact (hb.2 k hk z hz).trans_eq (by dsimp only [C,K,epsilon]; ring)
  · intro k hk z hz
    exact (hd.2 k hk z hz).trans_eq (by dsimp only [C,K,epsilon]; ring)

#print axioms parameterRound2_actual_globalMean_coefficient_jets
end GlobalEmbedding.Continuation
