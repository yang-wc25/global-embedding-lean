import Probes.ActualPhaseEuclideanChart
import Probes.ActualRefinementPartitionJets
import Probes.ActualRefinementTotalCount

/-!
# Actual quantitative adapted charts and their real subordinate partition

One construction selects the finite centers, the actual phase-adapted charts,
and the literal smooth cutoffs. A fixed construction radius yields a uniform
TOTAL number of pieces per original bounded chart. The same construction
works for every higher observation order. No adapted chart, inverse bound,
partition, cutoff budget or refinement count is supplied as an input.
-/

noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
attribute [local instance] Classical.propDecidable

def actualPhaseRefinementFactor (mu M : ℝ) : ℝ :=
  32*actualPhaseInverseConstant mu (2*M)*(1+2*M)

theorem actualPhaseRefinementFactor_pos {mu M : ℝ} (hmu : 0 < mu) (hM : 0 ≤ M) :
    0 < actualPhaseRefinementFactor mu M := by
  have hb : 1 ≤ actualPhaseInverseConstant mu (2*M) := actualPhaseInverseConstant_one_le hmu (by positivity)
  unfold actualPhaseRefinementFactor
  positivity

theorem actualPhaseRefinementFactor_radius (mu M rho : ℝ) :
    4*(rho/actualPhaseRefinementFactor mu M) = actualEuclideanPhaseRadius mu M rho := by
  unfold actualPhaseRefinementFactor actualEuclideanPhaseRadius
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep]
  {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

/-- Uniformity includes the total piece count. The fixed positive radius rho
is a construction buffer, not a later Nash iteration scale. -/
theorem actual_exists_uniform_quantitative_adapted_refinement_full_jets
    (mu M R rho : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hrho : 0 < rho) :
    ∃ L : ℕ, ∀ (psi : X → ℝ) (K O : Set X) (c0 : X),
      IsOpen O → K ⊆ closedBall c0 R →
      (∀ c ∈ K, ball c rho ⊆ O) →
      ContDiffOn ℝ ∞ psi O →
      (∀ c ∈ K, mu ≤ ‖(fderiv ℝ psi c).comp (ContinuousLinearMap.inr ℝ Ep D)‖) →
      (∀ x ∈ O, ‖fderiv ℝ psi x‖ ≤ M) →
      (∀ x ∈ O, rho*‖iteratedFDeriv ℝ 2 psi x‖ ≤ M) →
      ∃ (s : Finset X) (a : s → OpenPartialHomeomorph X X) (W : Set X),
        let r := rho/actualPhaseRefinementFactor mu M
        s.card ≤ L ∧ (↑s : Set X) ⊆ K ∧ IsOpen W ∧ K ⊆ W ∧
        (∀ x ∈ W, ∑ c ∈ s, actualRefinementCutoff X s r c x = 1) ∧
        (∀ c : s,
          (a c).source ⊆ O ∧
          ball c.val (4*r) ⊆ (a c).source ∧
          ContDiffOn ℝ ∞ (a c) (a c).source ∧
          ContDiffOn ℝ ∞ (a c).symm (a c).target ∧
          (∀ x ∈ (a c).source, ((a c) x).1 = x.1 ∧ ((a c) x).2 0 = psi x) ∧
          (∀ x ∈ (a c).target, ((a c).symm x).1 = x.1 ∧ psi ((a c).symm x) = x.2 0) ∧
          closedBall ((a c) c.val) (r/actualPhaseInverseConstant mu (2*M)) ⊆ (a c).target ∧
          (∀ x ∈ (a c).source, ‖fderiv ℝ (a c) x‖ ≤ 2*(1+2*M)) ∧
          tsupport (actualRefinementCutoff X s r c.val) ⊆ (a c).source ∧
          ContDiff ℝ ∞ (actualRefinementCutoff X s r c.val) ∧
          (∀ x, 0 ≤ actualRefinementCutoff X s r c.val x ∧ actualRefinementCutoff X s r c.val x ≤ 1)) ∧
        (∀ x : X,
          (s.filter (fun c => x ∈ tsupport (actualRefinementCutoff X s r c))).card ≤
            5^Module.finrank ℝ X) ∧
        (∀ (j : ℕ) (weight : ℝ), 0 ≤ weight → weight ≤ rho → ∀ (c : s) (x : X),
          weight^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r c.val) x‖ ≤
            (actualPhaseRefinementFactor mu M)^j * actualRefinementCutoffJetCost X j) ∧
        (∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
          (∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ O,
            weight^i*‖iteratedFDeriv ℝ (i+1) psi x‖ ≤ Mj) →
          ∀ (c : s) i, 1 ≤ i → i ≤ j → ∀ x ∈ (a c).source,
            weight^i*‖iteratedFDeriv ℝ (i+1) (a c) x‖ ≤ 2^(j+2)*Mj) ∧
        (∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
          (∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ O,
            weight^i*‖iteratedFDeriv ℝ (i+1) psi x‖ ≤ Mj) →
          ∀ (c : s) k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ (a c).target,
            weight^(k-1)*‖iteratedFDeriv ℝ k (a c).symm y‖ ≤
              actualEuclideanPhaseInverseJetCost mu M Mj j) := by
  classical
  let r := rho/actualPhaseRefinementFactor mu M
  have hfactor := actualPhaseRefinementFactor_pos hmu hM
  have hr : 0 < r := div_pos hrho hfactor
  obtain ⟨L,hL⟩ := actual_exists_uniform_total_refinement_bound X R r hr
  refine ⟨L,?_⟩
  intro psi K O c0 hO hKR hbuffer hpsi hnoncrit hfirst hsecond
  have hK : TotallyBounded K := (isCompact_closedBall c0 R).totallyBounded.subset hKR
  obtain ⟨s,hsK,hsep,hcover,hcount⟩ := actual_exists_finite_bounded_refinement K hK r hr
  have hcharts (c : s) := actual_exists_native_euclidean_quantitative_phase_chart_full_jets mu M hmu hM
    psi c.val rho hrho (hpsi.mono (hbuffer c.val (hsK c.property)))
    (hnoncrit c.val (hsK c.property))
    (fun x hx => hfirst x (hbuffer c.val (hsK c.property) hx))
    (fun x hx => hsecond x (hbuffer c.val (hsK c.property) hx))
  choose a ha using hcharts
  let W : Set X := {x | 1/2 < actualRefinementRawSum X s r x}
  have hW : IsOpen W := isOpen_lt continuous_const (actualRefinementRawSum_contDiff X s r).continuous
  have hKW : K ⊆ W := by
    intro x hx
    have hh := actualRefinementRawSum_lower_on_cover X s r hr K hcover x hx
    change 1/2 < actualRefinementRawSum X s r x
    linarith
  refine ⟨s,a,W,?_⟩
  dsimp only
  refine ⟨hL s c0 (fun c hc => hKR (hsK hc)) hsep,hsK,hW,hKW,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    rw [actualRefinementCutoff_sum]
    exact actualRefinementReciprocal_exact _ (le_of_lt hx)
  · intro c
    obtain ⟨hinner,houter,hsm,hinv,hparam,hback,htarget,hforward,_⟩ := ha c
    have hrad : 4*r = actualEuclideanPhaseRadius mu M rho := actualPhaseRefinementFactor_radius mu M rho
    have hsupport : tsupport (actualRefinementCutoff X s r c.val) ⊆ (a c).source := by
      apply (actualRefinementCutoff_tsupport X s r hr c.val).trans
      apply (closedBall_subset_ball (by linarith : 2*r < 4*r)).trans
      rw [hrad]
      exact hinner
    refine ⟨houter.trans (hbuffer c.val (hsK c.property)),?_,hsm,hinv,hparam,hback,?_,hforward,hsupport,
      actualRefinementCutoff_contDiff X s r c.val,fun x =>
        ⟨actualRefinementCutoff_nonneg X s r c.val x,actualRefinementCutoff_le_one X s r c.val c.property x⟩⟩
    · rwa [hrad]
    · have he : actualEuclideanPhaseRadius mu M rho/(4*actualPhaseInverseConstant mu (2*M)) =
          r/actualPhaseInverseConstant mu (2*M) := by rw [← hrad]; ring
      rwa [he] at htarget
  · intro x
    apply (Finset.card_le_card ?_).trans (hcount x)
    intro c hc
    obtain ⟨hcs,hxs⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hcs,?_⟩
    have hh := actualRefinementCutoff_tsupport X s r hr c hxs
    simpa only [mem_closedBall,dist_comm] using hh
  · intro j weight hweight hwrho c x
    have hb := actualRefinementCutoff_weighted_jet X s r hr hsep c.val x j
    have he : rho = actualPhaseRefinementFactor mu M*r := by
      dsimp only [r]
      field_simp
    calc
      _ ≤ rho^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r c.val) x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hweight hwrho j) (norm_nonneg _)
      _ = (actualPhaseRefinementFactor mu M)^j *
          (r^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r c.val) x‖) := by
            conv_lhs => arg 1; rw [he,mul_pow]
            ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (pow_nonneg hfactor.le j)
  · intro j weight Mj hweight hMj hjet c i hi hij x hx
    exact (ha c).2.2.2.2.2.2.2.2.1 j weight Mj hweight hMj
      (fun i hi hij x hx => hjet i hi hij x (hbuffer c.val (hsK c.property) hx)) i hi hij x hx
  · intro j weight Mj hweight hMj hjet c k hk hkj y hy
    exact (ha c).2.2.2.2.2.2.2.2.2 j weight Mj hweight hMj
      (fun i hi hij x hx => hjet i hi hij x (hbuffer c.val (hsK c.property) hx)) k hk hkj y hy

/-- Forward first bound and all inverse/cutoff jets, with the historical field order. -/
theorem actual_exists_uniform_quantitative_adapted_refinement_with_forward_bound
    (mu M R rho : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hrho : 0 < rho) :
    ∃ L : ℕ, ∀ (psi : X → ℝ) (K O : Set X) (c0 : X),
      IsOpen O → K ⊆ closedBall c0 R →
      (∀ c ∈ K, ball c rho ⊆ O) →
      ContDiffOn ℝ ∞ psi O →
      (∀ c ∈ K, mu ≤ ‖(fderiv ℝ psi c).comp (ContinuousLinearMap.inr ℝ Ep D)‖) →
      (∀ x ∈ O, ‖fderiv ℝ psi x‖ ≤ M) →
      (∀ x ∈ O, rho*‖iteratedFDeriv ℝ 2 psi x‖ ≤ M) →
      ∃ (s : Finset X) (a : s → OpenPartialHomeomorph X X) (W : Set X),
        let r := rho/actualPhaseRefinementFactor mu M
        s.card ≤ L ∧ (↑s : Set X) ⊆ K ∧ IsOpen W ∧ K ⊆ W ∧
        (∀ x ∈ W, ∑ c ∈ s, actualRefinementCutoff X s r c x = 1) ∧
        (∀ c : s,
          (a c).source ⊆ O ∧
          ball c.val (4*r) ⊆ (a c).source ∧
          ContDiffOn ℝ ∞ (a c) (a c).source ∧
          ContDiffOn ℝ ∞ (a c).symm (a c).target ∧
          (∀ x ∈ (a c).source, ((a c) x).1 = x.1 ∧ ((a c) x).2 0 = psi x) ∧
          (∀ x ∈ (a c).target, ((a c).symm x).1 = x.1 ∧ psi ((a c).symm x) = x.2 0) ∧
          closedBall ((a c) c.val) (r/actualPhaseInverseConstant mu (2*M)) ⊆ (a c).target ∧
          (∀ x ∈ (a c).source, ‖fderiv ℝ (a c) x‖ ≤ 2*(1+2*M)) ∧
          tsupport (actualRefinementCutoff X s r c.val) ⊆ (a c).source ∧
          ContDiff ℝ ∞ (actualRefinementCutoff X s r c.val) ∧
          (∀ x, 0 ≤ actualRefinementCutoff X s r c.val x ∧ actualRefinementCutoff X s r c.val x ≤ 1)) ∧
        (∀ x : X,
          (s.filter (fun c => x ∈ tsupport (actualRefinementCutoff X s r c))).card ≤
            5^Module.finrank ℝ X) ∧
        (∀ (j : ℕ) (weight : ℝ), 0 ≤ weight → weight ≤ rho → ∀ (c : s) (x : X),
          weight^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r c.val) x‖ ≤
            (actualPhaseRefinementFactor mu M)^j * actualRefinementCutoffJetCost X j) ∧
        (∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
          (∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ O,
            weight^i*‖iteratedFDeriv ℝ (i+1) psi x‖ ≤ Mj) →
          ∀ (c : s) k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ (a c).target,
            weight^(k-1)*‖iteratedFDeriv ℝ k (a c).symm y‖ ≤
              actualEuclideanPhaseInverseJetCost mu M Mj j) := by
  obtain ⟨L,hL⟩ := actual_exists_uniform_quantitative_adapted_refinement_full_jets
    (Ep := Ep) (m := m) mu M R rho hmu hM hrho
  refine ⟨L,?_⟩
  intro psi K O c0 hO hKR hbuffer hpsi hnoncrit hfirst hsecond
  obtain ⟨s,a,W,hcard,hsK,hW,hKW,hpart,hcharts,hcount,hcut,_hfwd,hjets⟩ :=
    hL psi K O c0 hO hKR hbuffer hpsi hnoncrit hfirst hsecond
  exact ⟨s,a,W,hcard,hsK,hW,hKW,hpart,hcharts,hcount,hcut,hjets⟩

/-- All-scales refinement with the historical field order. -/
theorem actual_exists_uniform_quantitative_adapted_refinement_all_scales
    (mu M R rho : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hrho : 0 < rho) :
    ∃ L : ℕ, ∀ (psi : X → ℝ) (K O : Set X) (c0 : X),
      IsOpen O → K ⊆ closedBall c0 R →
      (∀ c ∈ K, ball c rho ⊆ O) →
      ContDiffOn ℝ ∞ psi O →
      (∀ c ∈ K, mu ≤ ‖(fderiv ℝ psi c).comp (ContinuousLinearMap.inr ℝ Ep D)‖) →
      (∀ x ∈ O, ‖fderiv ℝ psi x‖ ≤ M) →
      (∀ x ∈ O, rho*‖iteratedFDeriv ℝ 2 psi x‖ ≤ M) →
      ∃ (s : Finset X) (a : s → OpenPartialHomeomorph X X) (W : Set X),
        let r := rho/actualPhaseRefinementFactor mu M
        s.card ≤ L ∧ (↑s : Set X) ⊆ K ∧ IsOpen W ∧ K ⊆ W ∧
        (∀ x ∈ W, ∑ c ∈ s, actualRefinementCutoff X s r c x = 1) ∧
        (∀ c : s,
          (a c).source ⊆ O ∧
          ball c.val (4*r) ⊆ (a c).source ∧
          ContDiffOn ℝ ∞ (a c) (a c).source ∧
          ContDiffOn ℝ ∞ (a c).symm (a c).target ∧
          (∀ x ∈ (a c).source, ((a c) x).1 = x.1 ∧ ((a c) x).2 0 = psi x) ∧
          (∀ x ∈ (a c).target, ((a c).symm x).1 = x.1 ∧ psi ((a c).symm x) = x.2 0) ∧
          closedBall ((a c) c.val) (r/actualPhaseInverseConstant mu (2*M)) ⊆ (a c).target ∧
          tsupport (actualRefinementCutoff X s r c.val) ⊆ (a c).source ∧
          ContDiff ℝ ∞ (actualRefinementCutoff X s r c.val) ∧
          (∀ x, 0 ≤ actualRefinementCutoff X s r c.val x ∧ actualRefinementCutoff X s r c.val x ≤ 1)) ∧
        (∀ x : X,
          (s.filter (fun c => x ∈ tsupport (actualRefinementCutoff X s r c))).card ≤
            5^Module.finrank ℝ X) ∧
        (∀ (j : ℕ) (weight : ℝ), 0 ≤ weight → weight ≤ rho → ∀ (c : s) (x : X),
          weight^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r c.val) x‖ ≤
            (actualPhaseRefinementFactor mu M)^j * actualRefinementCutoffJetCost X j) ∧
        (∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
          (∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ O,
            weight^i*‖iteratedFDeriv ℝ (i+1) psi x‖ ≤ Mj) →
          ∀ (c : s) k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ (a c).target,
            weight^(k-1)*‖iteratedFDeriv ℝ k (a c).symm y‖ ≤
              actualEuclideanPhaseInverseJetCost mu M Mj j) := by
  obtain ⟨L,hL⟩ := actual_exists_uniform_quantitative_adapted_refinement_with_forward_bound
    (Ep := Ep) (m := m) mu M R rho hmu hM hrho
  refine ⟨L,?_⟩
  intro psi K O c0 hO hKR hbuffer hpsi hnoncrit hfirst hsecond
  obtain ⟨s,a,W,hcard,hsK,hW,hKW,hpart,hcharts,hcount,hcut,hjets⟩ :=
    hL psi K O c0 hO hKR hbuffer hpsi hnoncrit hfirst hsecond
  refine ⟨s,a,W,hcard,hsK,hW,hKW,hpart,?_,hcount,hcut,hjets⟩
  intro c
  obtain ⟨ho,hi,hs,his,hf,hb,ht,_hfwd,hsup,hsm,hval⟩ := hcharts c
  exact ⟨ho,hi,hs,his,hf,hb,ht,hsup,hsm,hval⟩

/-- The construction-radius specialization of the same all-scales family. -/
theorem actual_exists_uniform_quantitative_adapted_refinement
    (mu M R rho : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hrho : 0 < rho) :
    ∃ L : ℕ, ∀ (psi : X → ℝ) (K O : Set X) (c0 : X),
      IsOpen O → K ⊆ closedBall c0 R →
      (∀ c ∈ K, ball c rho ⊆ O) →
      ContDiffOn ℝ ∞ psi O →
      (∀ c ∈ K, mu ≤ ‖(fderiv ℝ psi c).comp (ContinuousLinearMap.inr ℝ Ep D)‖) →
      (∀ x ∈ O, ‖fderiv ℝ psi x‖ ≤ M) →
      (∀ x ∈ O, rho*‖iteratedFDeriv ℝ 2 psi x‖ ≤ M) →
      ∃ (s : Finset X) (a : s → OpenPartialHomeomorph X X) (W : Set X),
        let r := rho/actualPhaseRefinementFactor mu M
        s.card ≤ L ∧ (↑s : Set X) ⊆ K ∧ IsOpen W ∧ K ⊆ W ∧
        (∀ x ∈ W, ∑ c ∈ s, actualRefinementCutoff X s r c x = 1) ∧
        (∀ c : s,
          (a c).source ⊆ O ∧
          ball c.val (4*r) ⊆ (a c).source ∧
          ContDiffOn ℝ ∞ (a c) (a c).source ∧
          ContDiffOn ℝ ∞ (a c).symm (a c).target ∧
          (∀ x ∈ (a c).source, ((a c) x).1 = x.1 ∧ ((a c) x).2 0 = psi x) ∧
          (∀ x ∈ (a c).target, ((a c).symm x).1 = x.1 ∧ psi ((a c).symm x) = x.2 0) ∧
          closedBall ((a c) c.val) (r/actualPhaseInverseConstant mu (2*M)) ⊆ (a c).target ∧
          tsupport (actualRefinementCutoff X s r c.val) ⊆ (a c).source ∧
          ContDiff ℝ ∞ (actualRefinementCutoff X s r c.val) ∧
          (∀ x, 0 ≤ actualRefinementCutoff X s r c.val x ∧ actualRefinementCutoff X s r c.val x ≤ 1)) ∧
        (∀ x : X,
          (s.filter (fun c => x ∈ tsupport (actualRefinementCutoff X s r c))).card ≤
            5^Module.finrank ℝ X) ∧
        (∀ (j : ℕ) (c : s) (x : X),
          rho^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r c.val) x‖ ≤
            (actualPhaseRefinementFactor mu M)^j * actualRefinementCutoffJetCost X j) ∧
        (∀ (j : ℕ) (Mj : ℝ), 0 ≤ Mj →
          (∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ O,
            rho^i*‖iteratedFDeriv ℝ (i+1) psi x‖ ≤ Mj) →
          ∀ (c : s) k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ (a c).target,
            rho^(k-1)*‖iteratedFDeriv ℝ k (a c).symm y‖ ≤
              actualEuclideanPhaseInverseJetCost mu M Mj j) := by
  obtain ⟨L,hL⟩ := actual_exists_uniform_quantitative_adapted_refinement_all_scales
    (Ep := Ep) (m := m) mu M R rho hmu hM hrho
  refine ⟨L,?_⟩
  intro psi K O c0 hO hKR hbuffer hpsi hnoncrit hfirst hsecond
  obtain ⟨s,a,W,hcard,hsK,hW,hKW,hpart,hcharts,hcount,hcut,hjets⟩ :=
    hL psi K O c0 hO hKR hbuffer hpsi hnoncrit hfirst hsecond
  exact ⟨s,a,W,hcard,hsK,hW,hKW,hpart,hcharts,hcount,
    fun j c x => hcut j rho hrho.le le_rfl c x,
    fun j Mj hMj hjet => hjets j rho Mj hrho hMj hjet⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_exists_uniform_quantitative_adapted_refinement

#print axioms GlobalEmbedding.Continuation.actual_exists_uniform_quantitative_adapted_refinement_all_scales

#print axioms GlobalEmbedding.Continuation.actual_exists_uniform_quantitative_adapted_refinement_with_forward_bound

#print axioms GlobalEmbedding.Continuation.actual_exists_uniform_quantitative_adapted_refinement_full_jets
