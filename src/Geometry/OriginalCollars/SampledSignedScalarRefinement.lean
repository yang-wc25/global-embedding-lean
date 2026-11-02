import OriginalCollars.CountedSignedScalarRefinement
import OriginalCollars.ActualSampledPhaseControls

/-! The same scalar-chart construction exposes a packing bound chosen
only from the low geometric data.  The actual separated centers carry the
complete forward/inverse profiles and weighted partition estimates. -/
noncomputable section
open GlobalEmbedding.Offline Set Function Filter Metric
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

private theorem sampled_signed_phase_profile_le_prefix (Phase : ℕ → ℝ) (hPhase : ∀ j, 0 ≤ Phase j)
    {k j : ℕ} (hkj : k ≤ j) : Phase k ≤ bufferedTransitionPrefix Phase j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hPhase l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem sampled_signed_scalar_refinement_complete_profiles
    (mu Mb R rho coordinateBound : ℝ) (Phase : ℕ → ℝ)
    (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hrho : 0 < rho)
    (hCoordinate : 0 ≤ coordinateBound) (hPhase : ∀ j, 0 ≤ Phase j)
    (hFirstBudget : Phase 1 ≤ Mb) (hSecondBudget : rho*Phase 2 ≤ Mb) :
    ∀ (psi : X → ℝ) (K O : Set X) (c0 : X),
      IsOpen O → K ⊆ closedBall c0 R →
      (∀ c ∈ K, ball c rho ⊆ O) →
      ContDiffOn ℝ ∞ psi O →
      (∀ c ∈ K, mu ≤ ‖(fderiv ℝ psi c).comp (ContinuousLinearMap.inr ℝ Ep D)‖) →
      (∀ x ∈ O, ‖x‖ ≤ coordinateBound) →
      (∀ j x, x ∈ O → ‖iteratedFDeriv ℝ j psi x‖ ≤ Phase j) →
      ∃ (s : Finset X) (a : s → OpenPartialHomeomorph X X) (W : Set X),
        let r := rho/actualPhaseRefinementFactor mu Mb
        s.card ≤ countedSignedTotalRefinementBound (Ep := Ep) (m := m)
          mu Mb R rho hmu hMb hrho ∧ (↑s : Set X) ⊆ K ∧ IsOpen W ∧ K ⊆ W ∧
        (∀ x ∈ W, ∑ c ∈ s, actualRefinementCutoff X s r c x = 1) ∧
        (∀ c : s,
          (a c).source ⊆ O ∧
          ball c.val (4*r) ⊆ (a c).source ∧
          ContDiffOn ℝ ∞ (a c) (a c).source ∧
          ContDiffOn ℝ ∞ (a c).symm (a c).target ∧
          (∀ x ∈ (a c).source, ((a c) x).1 = x.1 ∧ ((a c) x).2 0 = psi x) ∧
          (∀ x ∈ (a c).target, ((a c).symm x).1 = x.1 ∧ psi ((a c).symm x) = x.2 0) ∧
          tsupport (actualRefinementCutoff X s r c.val) ⊆ (a c).source ∧
          ContDiff ℝ ∞ (actualRefinementCutoff X s r c.val) ∧
          (∀ x, 0 ≤ actualRefinementCutoff X s r c.val x ∧ actualRefinementCutoff X s r c.val x ≤ 1)) ∧
        (∀ x : X,
          (s.filter (fun c => x ∈ tsupport (actualRefinementCutoff X s r c))).card ≤
            5^Module.finrank ℝ X) ∧
        (∀ j c x, x ∈ (a c).source →
          ‖iteratedFDeriv ℝ j (a c) x‖ ≤ incrementScalarForwardProfile Mb coordinateBound Phase j) ∧
        (∀ j c y, y ∈ (a c).target →
          ‖iteratedFDeriv ℝ j (a c).symm y‖ ≤ incrementScalarInverseProfile mu Mb coordinateBound Phase j) ∧
        (∀ j (weight : ℝ), 0 ≤ weight → weight ≤ rho → ∀ (c : s) (x : X),
          weight^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r c.val) x‖ ≤
            (actualPhaseRefinementFactor mu Mb)^j * actualRefinementCutoffJetCost X j) ∧
        (∀ c : s, ActualPhaseSampleJetControls mu Mb psi (a c)) := by
  let r := rho/actualPhaseRefinementFactor mu Mb
  have hfactor := actualPhaseRefinementFactor_pos hmu hMb
  have hr : 0 < r := div_pos hrho hfactor
  have hL := Classical.choose_spec (actual_exists_uniform_total_refinement_bound X R r hr)
  intro psi K O c0 hO hKR hbuffer hpsi hnoncrit hCoordinates hJets
  have hK : TotallyBounded K := (isCompact_closedBall c0 R).totallyBounded.subset hKR
  obtain ⟨s,hsK,hsep,hcover,hcount⟩ := actual_exists_finite_bounded_refinement K hK r hr
  have hcharts (c : s) := increment_actual_scalar_chart_with_values mu Mb hmu hMb psi c.val rho hrho
    (hpsi.mono (hbuffer c.val (hsK c.property))) (hnoncrit c.val (hsK c.property))
    (fun x hx => by
      have h := hJets 1 x (hbuffer c.val (hsK c.property) hx)
      rw [norm_iteratedFDeriv_one] at h
      exact h.trans hFirstBudget)
    (fun x hx => (mul_le_mul_of_nonneg_left (hJets 2 x
      (hbuffer c.val (hsK c.property) hx)) hrho.le).trans hSecondBudget)
  choose a ha using hcharts
  let W : Set X := {x | 1/2 < actualRefinementRawSum X s r x}
  have hW : IsOpen W := isOpen_lt continuous_const (actualRefinementRawSum_contDiff X s r).continuous
  have hKW : K ⊆ W := by
    intro x hx
    have hh := actualRefinementRawSum_lower_on_cover X s r hr K hcover x hx
    change 1/2 < actualRefinementRawSum X s r x
    linarith
  have hSource (c : s) : (a c).source ⊆ O :=
    (ha c).2.1.trans (hbuffer c.val (hsK c.property))
  refine ⟨s,a,W,?_⟩
  dsimp only
  refine ⟨hL s c0 (fun c hc => hKR (hsK hc)) hsep,hsK,hW,hKW,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    rw [actualRefinementCutoff_sum]
    exact actualRefinementReciprocal_exact _ (le_of_lt hx)
  · intro c
    obtain ⟨hinner,houter,hsm,hinv,hparam,hback,htarget,hpoint,hforward,hhigher,hij,hval,hival⟩ := ha c
    have hrad : 4*r = actualEuclideanPhaseRadius mu Mb rho := actualPhaseRefinementFactor_radius mu Mb rho
    have hsupport : tsupport (actualRefinementCutoff X s r c.val) ⊆ (a c).source := by
      apply (actualRefinementCutoff_tsupport X s r hr c.val).trans
      apply (closedBall_subset_ball (by linarith : 2*r < 4*r)).trans
      rwa [hrad]
    exact ⟨hSource c,by rwa [hrad],hsm,hinv,hparam,hback,hsupport,
      actualRefinementCutoff_contDiff X s r c.val,fun x =>
        ⟨actualRefinementCutoff_nonneg X s r c.val x,actualRefinementCutoff_le_one X s r c.val c.property x⟩⟩
  · intro x
    apply (Finset.card_le_card ?_).trans (hcount x)
    intro c hc
    obtain ⟨hcs,hxs⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hcs,?_⟩
    have hh := actualRefinementCutoff_tsupport X s r hr c hxs
    simpa only [mem_closedBall,dist_comm] using hh
  · intro j c x hx
    obtain ⟨hinner,houter,hsm,hinv,hparam,hback,htarget,hpoint,hforward,hhigher,hij,hval,hival⟩ := ha c
    by_cases hj0 : j=0
    · subst j
      simp only [incrementScalarForwardProfile,ite_true,norm_iteratedFDeriv_zero]
      apply (hval x).trans
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (hCoordinates x (hSource c hx))
        (by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hJets 0 x (hSource c hx))
    · by_cases hj1 : j=1
      · subst j
        simpa only [incrementScalarForwardProfile,show ¬(1:ℕ)=0 by omega,ite_false,ite_true,
          norm_iteratedFDeriv_one] using hforward x hx
      · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        have hk : 1 ≤ k := by omega
        have h := (hpoint k hk x hx).trans
          (mul_le_mul_of_nonneg_left (hJets (k+1) x (hSource c hx)) (by positivity))
        simpa only [incrementScalarForwardProfile,show ¬k+1=0 by omega,ite_false,
          show ¬k+1=1 by omega,Nat.succ_eq_add_one] using h
  · intro j c y hy
    obtain ⟨hinner,houter,hsm,hinv,hparam,hback,htarget,hpoint,hforward,hhigher,hij,hval,hival⟩ := ha c
    by_cases hj0 : j=0
    · subst j
      simp only [incrementScalarInverseProfile,ite_true,norm_iteratedFDeriv_zero]
      exact hCoordinates _ (hSource c ((a c).map_target hy))
    · have hP := one_le_bufferedTransitionPrefix hPhase j
      have h := hij (j-1) 1 (bufferedTransitionPrefix Phase j) zero_lt_one (zero_le_one.trans hP)
        (by
          intro i hi hij x hx
          simp only [one_pow,one_mul]
          exact (hJets (i+1) x (hbuffer c.val (hsK c.property) hx)).trans
            (sampled_signed_phase_profile_le_prefix Phase hPhase (by omega))) j (by omega) (by omega) y hy
      simpa only [incrementScalarInverseProfile,hj0,ite_false,one_pow,one_mul] using h
  · intro j weight hweight hwrho c x
    have hb := actualRefinementCutoff_weighted_jet X s r hr hsep c.val x j
    have he : rho = actualPhaseRefinementFactor mu Mb*r := by dsimp only [r]; field_simp
    calc
      _ ≤ rho^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r c.val) x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hweight hwrho j) (norm_nonneg _)
      _ = (actualPhaseRefinementFactor mu Mb)^j *
          (r^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r c.val) x‖) := by
            conv_lhs => arg 1; rw [he,mul_pow]
            ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (pow_nonneg hfactor.le j)
  · intro c
    obtain ⟨hinner,houter,hsm,hinv,hparam,hback,htarget,hpoint,hforward,hhigher,hij,hval,hival⟩ := ha c
    apply actual_sampled_phase_controls_of_bounds mu Mb hmu hMb psi (a c) hsm hinv hforward hpoint
    intro y hy
    have h := hij 0 1 0 (by norm_num) le_rfl (by intro k hk hk0; omega)
      1 le_rfl le_rfl y hy
    simpa only [Nat.sub_self,pow_zero,one_mul,norm_iteratedFDeriv_one] using h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.sampled_signed_scalar_refinement_complete_profiles
