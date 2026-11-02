import Probes.Round3PreparedInteractionGerms

/-! An ordinary parent partition is refined only where the two primary
supports interact. The parent need not be supported in that closed pair.
This construction retains the literal all-order coordinate and cutoff jets
of the SAME selected charts, with no compact maximum taken afterwards.
This is the actual compact finite chart construction needed by the secondary
correction; using a refinement of the entire parent would wrongly require
Good/noncriticality away from the interaction carrier. -/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function Filter Metric
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [FiniteDimensional ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

theorem round4_actual_host_interaction_refinement_germs_profiles
    (mu Mb R buffer : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer)
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (theta psi : Ep × M → ℝ) (W pair : Set (Ep × M)) (hW : IsOpen W)
    (hTheta : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta W)
    (K O : Set X) (center : X)
    (hThetaSupport : incrementsGlobalRelativeSupport W theta ⊆
      (actualOriginalHostJointChart (Ep := Ep) c).source)
    (hK : ∀ z ∈ incrementsGlobalRelativeSupport W theta ∩ pair,
      actualOriginalHostJointChart c z ∈ K)
    (hO : IsOpen O) (hKR : K ⊆ closedBall center R)
    (hOq : O ⊆ (actualOriginalHostJointChart (Ep := Ep) c).target)
    (hOW : MapsTo (actualOriginalHostJointChart (Ep := Ep) c).symm O W)
    (hbufferO : ∀ x ∈ K, ball x buffer ⊆ O)
    (hPsi : ContDiffOn ℝ ∞ (psi ∘ (actualOriginalHostJointChart (Ep := Ep) c).symm) O)
    (hnoncrit : ∀ x ∈ K, mu ≤ ‖(fderiv ℝ
      (psi ∘ (actualOriginalHostJointChart (Ep := Ep) c).symm) x).comp
        (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hfirst : ∀ x ∈ O, ‖fderiv ℝ (psi ∘ (actualOriginalHostJointChart (Ep := Ep) c).symm) x‖ ≤ Mb)
    (hsecond : ∀ x ∈ O, buffer*‖iteratedFDeriv ℝ 2
      (psi ∘ (actualOriginalHostJointChart (Ep := Ep) c).symm) x‖ ≤ Mb) :
    ∃ (s : Finset X) (b : s → OpenPartialHomeomorph X X)
      (e : s → Ep → OpenPartialHomeomorph M D),
      let q := actualOriginalHostJointChart (Ep := Ep) c
      let Psi := psi ∘ q.symm
      let radius := buffer/actualPhaseRefinementFactor mu Mb
      let eta := fun t : s => actualHostRefinementCutoff
        (actualOriginalHostJointChart (Ep := Ep) c) theta (actualRefinementCutoff X s radius t.val)
      (∀ t : s, ActualOriginalHostSliceData c (b t) psi (e t)) ∧
      (∀ t : s, (b t).source ⊆ O) ∧
      (∀ t : s, (actualHostAdaptedChart c (b t)).source ⊆ W) ∧
      (∀ t : s, IsCompact (tsupport (eta t))) ∧
      (∀ t : s, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (eta t)) ∧
      (∀ t : s, tsupport (eta t) ⊆ (actualHostAdaptedChart c (b t)).source ∩
        incrementsGlobalRelativeSupport W theta) ∧
      (∀ z ∈ W ∩ pair, ∑ t : s, eta t z = theta z) ∧
      (∀ z ∈ W ∩ pair, ∀ᶠ w in 𝓝 z, ∑ t : s, eta t w = theta w) ∧
      (∀ z, (Finset.univ.filter (fun t : s => z ∈ tsupport (eta t))).card ≤ 5^Module.finrank ℝ X) ∧
      (∀ t : s, ∀ z ∈ (b t).source, ‖fderiv ℝ (b t) z‖ ≤ 2*(1+2*Mb)) ∧
        (∀ (S : Set X) (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
          (∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ O ∩ S, weight^i*‖iteratedFDeriv ℝ (i+1) Psi x‖ ≤ Mj) →
          (∀ (t : s) x, x ∈ (b t).source → ‖fderiv ℝ (b t) x‖ ≤ 2*(1+2*Mb)) ∧
          (∀ (t : s) i, 1 ≤ i → i ≤ j → ∀ x ∈ (b t).source ∩ S,
            weight^i*‖iteratedFDeriv ℝ (i+1) (b t) x‖ ≤ 2^(j+2)*Mj) ∧
          (∀ (t : s) k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ (b t).target, (b t).symm y ∈ S →
            weight^(k-1)*‖iteratedFDeriv ℝ k (b t).symm y‖ ≤
              actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j) ∧
          (∀ Mt : ℝ, 0 ≤ Mt → weight ≤ buffer →
            (∀ i, i ≤ j → ∀ x ∈ O ∩ S, weight^i*‖iteratedFDeriv ℝ i (theta ∘ q.symm) x‖ ≤ Mt) →
            ∀ (t : s) y, y ∈ (b t).target → (b t).symm y ∈ S →
              weight^j*‖iteratedFDeriv ℝ j (eta t ∘ (actualHostAdaptedChart c (b t)).symm) y‖ ≤
                actualHostRefinementSampleCutoffCost X mu Mb Mj Mt j)) := by
  let q := actualOriginalHostJointChart (Ep := Ep) c
  let Psi := psi ∘ q.symm
  obtain ⟨L,hL⟩ := actual_exists_uniform_quantitative_adapted_refinement_sample_jets
    (Ep := Ep) (m := m) mu Mb R buffer hmu hMb hbuffer
  obtain ⟨s,b,V,hcard,hsK,hV,hKV,hpart,hcharts,hcount,hcut,hforward,hjets⟩ :=
    hL Psi K O center hO hKR hbufferO hPsi hnoncrit hfirst hsecond
  let radius := buffer/actualPhaseRefinementFactor mu Mb
  let eta := fun t : s => actualHostRefinementCutoff q theta (actualRefinementCutoff X s radius t.val)
  have hhost (t : s) : ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData c (b t) psi e := by
    obtain ⟨ho,hi,hb,hbi,hp,hback,ht,hDf,hsup,hsm,hval⟩ := hcharts t
    obtain ⟨hat,ha,hai,hforw,e,he⟩ := actual_adapted_chart_original_host c hc psi (b t)
      (ho.trans hOq) hb hbi (fun z hz => (hp z hz).1) (fun z hz => (hp z hz).2)
    exact ⟨e,hat,ha,hai,hforw,he⟩
  choose e he using hhost
  have hSourceW (t : s) : (actualHostAdaptedChart c (b t)).source ⊆ W := by
    intro z hz
    have hw := hOW ((hcharts t).1 hz.2)
    change q.symm (q z) ∈ W at hw
    rwa [q.left_inv hz.1] at hw
  have hNative (t : s) : tsupport (actualRefinementCutoff X s radius t.val) ⊆ (b t).source ∧
      (b t).source ⊆ q.target :=
    ⟨(hcharts t).2.2.2.2.2.2.2.2.1,(hcharts t).1.trans hOq⟩
  have hRadius : 0 < radius := div_pos hbuffer (actualPhaseRefinementFactor_pos hmu hMb)
  have hAbsolute := actual_original_host_refinement_compact_cutoffs c hc theta W hW hTheta
    s b radius hRadius hThetaSupport hSourceW hNative
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
  have hSupport (t : s) : tsupport (eta t) ⊆
      incrementsGlobalRelativeSupport W theta ∩ (q.source ∩ q ⁻¹' tsupport (actualRefinementCutoff X s radius t.val)) := by
    have hh := (actual_host_cutoff_smooth_supported q theta (actualRefinementCutoff X s radius t.val)
      W hW hTheta hThetaSupport hq (actualRefinementCutoff_contDiff X s radius t.val)).2
    rwa [(hAbsolute t).2.2.2.2] at hh
  refine ⟨s,b,e,he,fun t => (hcharts t).1,hSourceW,
    fun t => (hAbsolute t).1,fun t => (hAbsolute t).2.1,
    fun t => (hAbsolute t).2.2.2.1,?_,?_,?_,fun t => (hcharts t).2.2.2.2.2.2.2.1,?_⟩
  · intro z hz
    by_cases hzk : z ∈ incrementsGlobalRelativeSupport W theta
    · have hzq := hThetaSupport hzk
      have hsum := hpart (q z) (hKV (hK z ⟨hzk,hz.2⟩))
      have hsum' : ∑ t : s, actualRefinementCutoff X s radius t.val (q z) = 1 :=
        (Finset.sum_coe_sort s (fun x : X => actualRefinementCutoff X s radius x (q z))).trans hsum
      change (∑ t : s, if z ∈ q.source then theta z*actualRefinementCutoff X s radius t.val (q z) else 0) = theta z
      simp only [if_pos (show z ∈ q.source from hzq)]
      rw [← Finset.mul_sum,hsum',mul_one]
    · have htheta : theta z = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun w : W => theta w.val) (x := ⟨z,hz.1⟩)
        exact fun hs => hzk ⟨⟨z,hz.1⟩,hs,rfl⟩
      change (∑ t : s, if z ∈ q.source then theta z*actualRefinementCutoff X s radius t.val (q z) else 0) = theta z
      simp only [htheta,zero_mul,ite_self,Finset.sum_const_zero]
  · intro z hz
    by_cases hzk : z ∈ incrementsGlobalRelativeSupport W theta
    · have hzq := hThetaSupport hzk
      have hzV := hKV (hK z ⟨hzk,hz.2⟩)
      filter_upwards [q.open_source.mem_nhds hzq,
        (q.continuousAt hzq).eventually (hV.mem_nhds hzV)] with w hwq hwV
      have hsum' : ∑ t : s, actualRefinementCutoff X s radius t.val (q w) = 1 :=
        (Finset.sum_coe_sort s (fun x : X => actualRefinementCutoff X s radius x (q w))).trans (hpart (q w) hwV)
      change (∑ t : s, if w ∈ q.source then theta w*actualRefinementCutoff X s radius t.val (q w) else 0) = theta w
      simp only [if_pos (show w ∈ q.source from hwq)]
      rw [← Finset.mul_sum,hsum',mul_one]
    · have hznt : z ∉ tsupport theta := by
        intro hh
        apply hzk
        rw [parameterRound2_global_relativeSupport_eq W hW]
        exact ⟨hz.1,hh⟩
      filter_upwards [(isClosed_tsupport theta).isOpen_compl.mem_nhds hznt] with w hw
      have htheta : theta w = 0 := image_eq_zero_of_notMem_tsupport hw
      change (∑ t : s, if w ∈ q.source then theta w*actualRefinementCutoff X s radius t.val (q w) else 0) = theta w
      simp only [htheta,zero_mul,ite_self,Finset.sum_const_zero]
  · intro z
    let active := Finset.univ.filter (fun t : s => z ∈ tsupport (eta t))
    let native := s.filter (fun x => q z ∈ tsupport (actualRefinementCutoff X s radius x))
    have himage : active.image (fun t : s => t.val) ⊆ native := by
      intro x hx
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨t.property,(hSupport t (Finset.mem_filter.mp ht).2).2.2⟩
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
        (actualRefinementCutoff X s radius t.val) (b t) O hO hOq (hcharts t).1 hThetaCoord
        (actualRefinementCutoff_contDiff X s radius t.val) (hcharts t).2.2.2.1
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

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4_actual_host_interaction_refinement_germs_profiles
