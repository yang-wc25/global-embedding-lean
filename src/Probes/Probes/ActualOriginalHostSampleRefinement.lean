import Probes.ActualOriginalHostRefinement
import Probes.ActualHostRefinementSampleJets
import Probes.ActualQuantitativeSampleRefinement

/-!
# Original host construction with sample-only higher-order budgets

The original host, its actual cutoff, and original phase data produce the
finite adapted charts and the literal subordinate cutoffs. The total piece
count is chosen before these fields. The same family works for all later
weights and derivative orders. Genuine slices and both true coordinate
transitions are outputs of the construction.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function Filter Metric
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

def actualHostRefinementSampleCutoffCost
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (mu Mb Mj Mt : ℝ) (j : ℕ) : ℝ :=
  actualFastChartTransferCost (fun _ => actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j) j *
    (2^j*(‖ContinuousLinearMap.mul ℝ ℝ‖*Mt)*actualHostRefinementCutoffPrefix E mu Mb j)

theorem actual_exists_original_host_sample_refinement_with_native_support
    (mu Mb R rho : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hrho : 0 < rho) :
    ∃ L : ℕ, ∀
      (c : OpenPartialHomeomorph M D) (_hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
      (theta psi : Ep × M → ℝ) (W : Set (Ep × M)) (_hW : IsOpen W)
      (_hTheta : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta W)
      (K O : Set X) (c0 : X),
      let q := actualOriginalHostJointChart (Ep := Ep) c
      let Psi := psi ∘ q.symm
      incrementsGlobalRelativeSupport W theta ⊆ q.source →
      (∀ z ∈ incrementsGlobalRelativeSupport W theta, q z ∈ K) →
      IsOpen O → K ⊆ closedBall c0 R → O ⊆ q.target → MapsTo q.symm O W →
      (∀ x ∈ K, ball x rho ⊆ O) → ContDiffOn ℝ ∞ Psi O →
      (∀ x ∈ K, mu ≤ ‖(fderiv ℝ Psi x).comp (ContinuousLinearMap.inr ℝ Ep D)‖) →
      (∀ x ∈ O, ‖fderiv ℝ Psi x‖ ≤ Mb) →
      (∀ x ∈ O, rho*‖iteratedFDeriv ℝ 2 Psi x‖ ≤ Mb) →
      ∃ (s : Finset X) (b : s → OpenPartialHomeomorph X X)
        (e : s → Ep → OpenPartialHomeomorph M D),
        let r := rho/actualPhaseRefinementFactor mu Mb
        let eta := fun t : s => actualHostRefinementCutoff q theta (actualRefinementCutoff X s r t.val)
        s.card ≤ L ∧
        (∀ t : s, ActualOriginalHostSliceData c (b t) psi (e t)) ∧
        (∀ t : s, (actualHostAdaptedChart c (b t)).source ⊆ W) ∧
        (∀ t : s, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (eta t) W) ∧
        (∀ t : s, incrementsGlobalRelativeSupport W (eta t) ⊆
          (actualHostAdaptedChart c (b t)).source ∩ incrementsGlobalRelativeSupport W theta) ∧
        (∀ z ∈ W, ∑ t : s, eta t z = theta z) ∧
        (∀ z ∈ W, (Finset.univ.filter (fun t : s => z ∈ incrementsGlobalRelativeSupport W (eta t))).card ≤
          5^Module.finrank ℝ X) ∧
        (∀ (j : ℕ) (weight : ℝ), 0 ≤ weight → weight ≤ rho → ∀ (t : s) x,
          weight^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r t.val) x‖ ≤
            (actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost X j) ∧
        (∀ t : s, tsupport (actualRefinementCutoff X s r t.val) ⊆ (b t).source ∧
          (b t).source ⊆ q.target) ∧
        (∀ (S : Set X) (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
          (∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ O ∩ S, weight^i*‖iteratedFDeriv ℝ (i+1) Psi x‖ ≤ Mj) →
          (∀ (t : s) x, x ∈ (b t).source → ‖fderiv ℝ (b t) x‖ ≤ 2*(1+2*Mb)) ∧
          (∀ (t : s) i, 1 ≤ i → i ≤ j → ∀ x ∈ (b t).source ∩ S,
            weight^i*‖iteratedFDeriv ℝ (i+1) (b t) x‖ ≤ 2^(j+2)*Mj) ∧
          (∀ (t : s) k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ (b t).target, (b t).symm y ∈ S →
            weight^(k-1)*‖iteratedFDeriv ℝ k (b t).symm y‖ ≤
              actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j) ∧
          (∀ Mt : ℝ, 0 ≤ Mt → weight ≤ rho →
            (∀ i, i ≤ j → ∀ x ∈ O ∩ S, weight^i*‖iteratedFDeriv ℝ i (theta ∘ q.symm) x‖ ≤ Mt) →
            ∀ (t : s) y, y ∈ (b t).target → (b t).symm y ∈ S →
              weight^j*‖iteratedFDeriv ℝ j (eta t ∘ (actualHostAdaptedChart c (b t)).symm) y‖ ≤
                actualHostRefinementSampleCutoffCost X mu Mb Mj Mt j)) := by
  obtain ⟨L,hL⟩ := actual_exists_uniform_quantitative_adapted_refinement_sample_jets
    (Ep := Ep) (m := m) mu Mb R rho hmu hMb hrho
  refine ⟨L,?_⟩
  intro c hc theta psi W hW hTheta K O c0 q Psi hThetaSupport hK hO hKR hOq hOW
    hbuffer hPsi hnoncrit hfirst hsecond
  obtain ⟨s,b,V,hcard,hsK,hV,hKV,hpart,hcharts,hcount,hcut,hforward,hjets⟩ :=
    hL Psi K O c0 hO hKR hbuffer hPsi hnoncrit hfirst hsecond
  let r := rho/actualPhaseRefinementFactor mu Mb
  let eta := fun t : s => actualHostRefinementCutoff q theta (actualRefinementCutoff X s r t.val)
  have hhost (t : s) : ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData c (b t) psi e := by
    obtain ⟨ho,hi,hb,hbi,hp,hback,ht,hDf,hsup,hsm,hval⟩ := hcharts t
    obtain ⟨hat,ha,hai,hforw,e,he⟩ := actual_adapted_chart_original_host c hc psi (b t)
      (ho.trans hOq) hb hbi (fun z hz => (hp z hz).1) (fun z hz => (hp z hz).2)
    exact ⟨e,hat,ha,hai,hforw,he⟩
  choose e he using hhost
  have hq : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ q q.source := by
    have hcs : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓙 ∞
        (fun z : Ep × M => c z.2) q.source :=
      (contMDiffOn_of_mem_maximalAtlas hc).comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2)
    exact contMDiffOn_fst.prodMk_space hcs
  have hqi : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ q.symm q.target := by
    have hcs : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞ (fun z : X => c.symm z.2) q.target :=
      (contMDiffOn_symm_of_mem_maximalAtlas hc).comp contDiff_snd.contMDiff.contMDiffOn
        (fun _ hz => hz.2)
    exact contDiff_fst.contMDiff.contMDiffOn.prodMk hcs
  have hThetaCoord : ContDiffOn ℝ ∞ (theta ∘ q.symm) O :=
    (hTheta.comp (hqi.mono hOq) hOW).contDiffOn
  have hfactor := (actualPhaseRefinementFactor_pos hmu hMb).le
  have hcost (i : ℕ) : 0 ≤ (actualPhaseRefinementFactor mu Mb)^i*actualRefinementCutoffJetCost X i :=
    mul_nonneg (pow_nonneg hfactor i) (actualRefinementCutoffJetCost_nonneg X i)
  have hprefix (j : ℕ) : 0 ≤ actualHostRefinementCutoffPrefix X mu Mb j :=
    Finset.sum_nonneg (fun i _ => hcost i)
  have hsmooth (t : s) := actual_host_cutoff_smooth_supported q theta
    (actualRefinementCutoff X s r t.val) W hW hTheta hThetaSupport hq
    (actualRefinementCutoff_contDiff X s r t.val)
  have hsupport (t : s) : incrementsGlobalRelativeSupport W (eta t) ⊆
      (actualHostAdaptedChart c (b t)).source ∩ incrementsGlobalRelativeSupport W theta := by
    intro z hz
    have hh := (hsmooth t).2 hz
    have hmodel := (hcharts t).2.2.2.2.2.2.2.2.1 hh.2.2
    exact ⟨⟨hh.2.1,hmodel⟩,hh.1⟩
  refine ⟨s,b,e,hcard,he,?_,fun t => (hsmooth t).1,hsupport,?_,?_,hcut,
    (fun t => ⟨(hcharts t).2.2.2.2.2.2.2.2.1,(hcharts t).1.trans hOq⟩),?_⟩
  · intro t z hz
    have ho := (hcharts t).1 hz.2
    have hw := hOW ho
    change q.symm (q z) ∈ W at hw
    rwa [q.left_inv hz.1] at hw
  · intro z hz
    by_cases hzk : z ∈ incrementsGlobalRelativeSupport W theta
    · have hzq := hThetaSupport hzk
      have hsum := hpart (q z) (hKV (hK z hzk))
      have hsum' : ∑ t : s, actualRefinementCutoff X s r t.val (q z) = 1 := by
        exact (Finset.sum_coe_sort s (fun x : X => actualRefinementCutoff X s r x (q z))).trans hsum
      change (∑ t : s, if z ∈ q.source then theta z*actualRefinementCutoff X s r t.val (q z) else 0) = theta z
      simp_rw [ite_eq_left hzq]
      rw [← Finset.mul_sum,hsum',mul_one]
    · have htheta : theta z = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun w : W => theta w.val) (x := ⟨z,hz⟩)
        exact fun hs => hzk ⟨⟨z,hz⟩,hs,rfl⟩
      change (∑ t : s, if z ∈ q.source then theta z*actualRefinementCutoff X s r t.val (q z) else 0) = theta z
      simp only [htheta,zero_mul,ite_self,Finset.sum_const_zero]
  · intro z hz
    let active := Finset.univ.filter (fun t : s => z ∈ incrementsGlobalRelativeSupport W (eta t))
    let native := s.filter (fun x => q z ∈ tsupport (actualRefinementCutoff X s r x))
    have himage : active.image (fun t : s => t.val) ⊆ native := by
      intro x hx
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨t.property,((hsmooth t).2 (Finset.mem_filter.mp ht).2).2.2⟩
    have hcard' := Finset.card_le_card himage
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard'
    exact hcard'.trans (hcount (q z))
  · intro S j weight Mj hweight hMj hjet
    have hInvJets (t : s) (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j+1)
        (y : X) (hy : y ∈ (b t).target) (hyS : (b t).symm y ∈ S) :
        weight^(k-1)*‖iteratedFDeriv ℝ k (b t).symm y‖ ≤
          actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j := by
      apply hjets t {z | z ∈ (b t).target ∧ (b t).symm z ∈ S}
        (fun _ hz => hz.1) j weight Mj hweight hMj ?_ k hk hkj y ⟨hy,hyS⟩
      intro i hi hij x hx
      obtain ⟨z,hz,rfl⟩ := hx
      exact hjet i hi hij _ ⟨(hcharts t).1 ((b t).map_target hz.1),hz.2⟩
    refine ⟨fun t => (hcharts t).2.2.2.2.2.2.2.1,?_,hInvJets,?_⟩
    · intro t i hi hij x hx
      calc
        _ ≤ weight^i*(2^(i+2)*‖iteratedFDeriv ℝ (i+1) Psi x‖) :=
          mul_le_mul_of_nonneg_left (hforward t i hi x hx.1) (pow_nonneg hweight.le i)
        _ = 2^(i+2)*(weight^i*‖iteratedFDeriv ℝ (i+1) Psi x‖) := by ring
        _ ≤ 2^(i+2)*Mj := mul_le_mul_of_nonneg_left
          (hjet i hi hij x ⟨(hcharts t).1 hx.1,hx.2⟩) (by positivity)
        _ ≤ 2^(j+2)*Mj := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (by omega)) hMj
    · intro Mt hMt hwle hThetaJet t y hy hyS
      have hInvCost := actualEuclideanPhaseSampleInverseJetCost_nonneg hmu hMb hMj j
      apply actual_host_refinement_cutoff_adapted_jets_at q theta
        (actualRefinementCutoff X s r t.val) (b t) O hO hOq (hcharts t).1 hThetaCoord
        (actualRefinementCutoff_contDiff X s r t.val) (hcharts t).2.2.2.1
        j weight Mt (actualHostRefinementCutoffPrefix X mu Mb j) hweight hMt (hprefix j)
        (fun _ => actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j) (fun _ => hInvCost)
        y hy ?_ ?_ ?_
      · intro i hij
        exact hThetaJet i hij _ ⟨(hcharts t).1 ((b t).map_target hy),hyS⟩
      · intro i hij x
        apply (hcut i weight hweight.le hwle t x).trans
        exact Finset.single_le_sum (fun k _ => hcost k) (by simpa using hij)
      · intro i hi hij
        exact hInvJets t i hi (by omega) y hy hyS


theorem actual_exists_original_host_sample_refinement
    (mu Mb R rho : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hrho : 0 < rho) :
    ∃ L : ℕ, ∀
      (c : OpenPartialHomeomorph M D) (_hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
      (theta psi : Ep × M → ℝ) (W : Set (Ep × M)) (_hW : IsOpen W)
      (_hTheta : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta W)
      (K O : Set X) (c0 : X),
      let q := actualOriginalHostJointChart (Ep := Ep) c
      let Psi := psi ∘ q.symm
      incrementsGlobalRelativeSupport W theta ⊆ q.source →
      (∀ z ∈ incrementsGlobalRelativeSupport W theta, q z ∈ K) →
      IsOpen O → K ⊆ closedBall c0 R → O ⊆ q.target → MapsTo q.symm O W →
      (∀ x ∈ K, ball x rho ⊆ O) → ContDiffOn ℝ ∞ Psi O →
      (∀ x ∈ K, mu ≤ ‖(fderiv ℝ Psi x).comp (ContinuousLinearMap.inr ℝ Ep D)‖) →
      (∀ x ∈ O, ‖fderiv ℝ Psi x‖ ≤ Mb) →
      (∀ x ∈ O, rho*‖iteratedFDeriv ℝ 2 Psi x‖ ≤ Mb) →
      ∃ (s : Finset X) (b : s → OpenPartialHomeomorph X X)
        (e : s → Ep → OpenPartialHomeomorph M D),
        let r := rho/actualPhaseRefinementFactor mu Mb
        let eta := fun t : s => actualHostRefinementCutoff q theta (actualRefinementCutoff X s r t.val)
        s.card ≤ L ∧
        (∀ t : s, ActualOriginalHostSliceData c (b t) psi (e t)) ∧
        (∀ t : s, (actualHostAdaptedChart c (b t)).source ⊆ W) ∧
        (∀ t : s, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (eta t) W) ∧
        (∀ t : s, incrementsGlobalRelativeSupport W (eta t) ⊆
          (actualHostAdaptedChart c (b t)).source ∩ incrementsGlobalRelativeSupport W theta) ∧
        (∀ z ∈ W, ∑ t : s, eta t z = theta z) ∧
        (∀ z ∈ W, (Finset.univ.filter (fun t : s => z ∈ incrementsGlobalRelativeSupport W (eta t))).card ≤
          5^Module.finrank ℝ X) ∧
        (∀ (j : ℕ) (weight : ℝ), 0 ≤ weight → weight ≤ rho → ∀ (t : s) x,
          weight^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r t.val) x‖ ≤
            (actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost X j) ∧
        (∀ (S : Set X) (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
          (∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ O ∩ S, weight^i*‖iteratedFDeriv ℝ (i+1) Psi x‖ ≤ Mj) →
          (∀ (t : s) x, x ∈ (b t).source → ‖fderiv ℝ (b t) x‖ ≤ 2*(1+2*Mb)) ∧
          (∀ (t : s) i, 1 ≤ i → i ≤ j → ∀ x ∈ (b t).source ∩ S,
            weight^i*‖iteratedFDeriv ℝ (i+1) (b t) x‖ ≤ 2^(j+2)*Mj) ∧
          (∀ (t : s) k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ (b t).target, (b t).symm y ∈ S →
            weight^(k-1)*‖iteratedFDeriv ℝ k (b t).symm y‖ ≤
              actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j) ∧
          (∀ Mt : ℝ, 0 ≤ Mt → weight ≤ rho →
            (∀ i, i ≤ j → ∀ x ∈ O ∩ S, weight^i*‖iteratedFDeriv ℝ i (theta ∘ q.symm) x‖ ≤ Mt) →
            ∀ (t : s) y, y ∈ (b t).target → (b t).symm y ∈ S →
              weight^j*‖iteratedFDeriv ℝ j (eta t ∘ (actualHostAdaptedChart c (b t)).symm) y‖ ≤
                actualHostRefinementSampleCutoffCost X mu Mb Mj Mt j)) := by
  obtain ⟨L,hL⟩ := actual_exists_original_host_sample_refinement_with_native_support
    (Ep := Ep) (m := m) (M := M) mu Mb R rho hmu hMb hrho
  refine ⟨L,?_⟩
  intro c hc theta psi W hW hTheta K O c0 q Psi hThetaSupport hK hO hKR hOq hOW
    hbuffer hPsi hnoncrit hfirst hsecond
  obtain ⟨s,b,e,hcard,he,hSourceW,hSmooth,hSupport,hPart,hCount,hCut,_hNative,hJets⟩ :=
    hL c hc theta psi W hW hTheta K O c0 hThetaSupport hK hO hKR hOq hOW
      hbuffer hPsi hnoncrit hfirst hsecond
  exact ⟨s,b,e,hcard,he,hSourceW,hSmooth,hSupport,hPart,hCount,hCut,hJets⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_exists_original_host_sample_refinement

#print axioms GlobalEmbedding.Continuation.actual_exists_original_host_sample_refinement_with_native_support
