import Probes.ActualSecondaryOriginalRawFamily
import Probes.ActualSecondaryOriginalObserverBinding
import Probes.ActualSecondaryPrimaryRawConsumers
import Probes.ActualSecondaryOppositeRegularity
import Probes.ActualSecondaryOriginalDerivative
import Probes.ActualSecondaryOriginalMean
import Probes.ActualSecondaryThreeTermMetricJets

/-! The SAME global primary and secondary maps, constructed entirely from raw
original fields and actual chosen chart data, satisfy the three-term metric
remainder bound. The physical primary/secondary errors, forcing and displacement
budgets are all produced inside the proof. The only omitted term is the SAME
native finite mean defect, whose original atlas estimate is supplied by the
actual finite mean iteration. No desired error estimate is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Tr Label SubPrimary SubSecondary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance rawRemainderTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance rawRemainderTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawRemainderTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

 theorem actual_original_raw_metric_remainder
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (Ep × M)) (primary : Label → Set (Ep × M)) (ell delta tau Delta : ℝ)
      (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
      (geom : ActualSecondarySignedRecord Label → SubSecondary → ActualSecondaryRawGeometry F hF nSolve (j+1) ell Mg W)
      (hcChoice : ∀ r a, (geom r a).c = (choice r a).c)
      (hChartChoice : ∀ r a, (geom r a).chart = (choice r a).chart)
      (hPhaseChoice : ∀ r a, (geom r a).phase = actualOriginalSecondaryPhase F g r.val)
      (hHost : ∀ r a, ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ (choice r a).host (choice r a).host.source)
      (hHostInv : ∀ r a, ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ (choice r a).host.symm (choice r a).host.target)
      (hHostSource : ∀ r a, (geom r a).chart.source ⊆
        ((OpenPartialHomeomorph.refl Ep).prod (choice r a).host).source)
      (hSupport : ∀ r a, tsupport (fun y : W => (choice r a).cutoff y.val) ∩
        Subtype.val ⁻¹' (incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
          incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2)) ⊆
        Subtype.val ⁻¹' (geom r a).support)
      (hPair : ∀ r a, (geom r a).support ⊆ incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
        incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2))
      (hPartition : ∀ r : ActualSecondarySignedRecord Label, ∀ y,
        y ∈ incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
          incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2) → ∑ a, (choice r a).cutoff y = 1),
      let host := fun r a => (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      let transition := fun r a => (host r a).symm.trans (geom r a).chart
      let cutoff := fun r a => (choice r a).cutoff ∘ (host r a).symm
      ∀ (hCut : ∀ r a, ContDiffOn ℝ ∞ (cutoff r a) (transition r a).source)
        (hInv : ∀ r a, ContDiffOn ℝ ∞ (transition r a).symm (transition r a).target)
        (rawHost : ∀ r a, ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) nSolve Rsub Lprimary
          reserve Bnd Mg T F hF g input inputbar W primary (choice r a).host (transition r a).source
          ((transition r a).symm '' (geom r a).sample) tau ell Delta)
        (hcut : ∀ r a k, k ≤ nSolve → ∀ z ∈ (geom r a).sample,
          ell^k*‖iteratedFDeriv ℝ k (cutoff r a) ((transition r a).symm z)‖ ≤ Kcut)
        (hinv : ∀ r a k, 1 ≤ k → k ≤ nSolve+1 → ∀ z ∈ (geom r a).sample,
          ell^(k-1)*‖iteratedFDeriv ℝ k (transition r a).symm z‖ ≤ Tinv k)
        (e : OpenPartialHomeomorph M D)
        (he : ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ e e.source)
        (heInv : ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ e.symm e.target)
        (Omega S : Set X)
        (rawObs : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) j Rsub Lprimary
          reserve Bnd Mg T F hF g input inputbar W primary e Omega S tau ell Delta)
        (hTarget : ∀ z ∈ Omega, z.2 ∈ e.target)
        (hFobs : ContDiffOn ℝ ∞ (fun z : X => F z.1 (e.symm z.2)) Omega)
        (pgeom : ActualOriginalPrimaryPhysicalGeometry F hF g),
      let b := (OpenPartialHomeomorph.refl Ep).prod e
      ∀ (hTransition : ∀ r a, ContDiffOn ℝ ∞ (b.symm.trans (geom r a).chart) (b.symm.trans (geom r a).chart).source)
        (hInverse : ∀ r a, ContDiffOn ℝ ∞ (b.symm.trans (geom r a).chart).symm (b.symm.trans (geom r a).chart).target)
        (O : ActualSecondarySignedRecord Label → SubSecondary → Set X)
        (hO : ∀ r a, IsOpen (O r a)) (hOOmega : ∀ r a, O r a ⊆ Omega)
        (hActive : ∀ r a, S ∩ b.symm ⁻¹' (geom r a).support ⊆ O r a)
        (hSource : ∀ r a, MapsTo b.symm (O r a) (geom r a).chart.source)
        (hSample : ∀ r a z, z ∈ S ∩ b.symm ⁻¹' (geom r a).support →
          (geom r a).chart (b.symm z) ∈ (geom r a).sample)
        (hTransitionBound : ∀ r a z, z ∈ S ∩ b.symm ⁻¹' (geom r a).support → ∀ k,
          1 ≤ k → k ≤ j+2 → ell^(k-1)*‖iteratedFDeriv ℝ k ((geom r a).chart ∘ b.symm) z‖ ≤ Tobs k)
        (hCount : ∀ r : ActualSecondarySignedRecord Label, ∀ z ∈ S,
          (Finset.univ.filter (fun a => b.symm z ∈ (geom r a).support)).card ≤ Rsecondary),
      let U := fun y => delta • incrementsGlobalPrimaryWave F hF g input (q+2) tau y+
        actualOriginalSecondarySum F hF g input (q+2) tau delta choice y
      let Mean := fun z : X => delta^2 • actualRealTensorAssembly (fun i j =>
        (incrementsGlobalPrimaryMean F hF g input (q+2) tau z.1 (e.symm z.2)
          (incrementsGlobalObservationVector (I := 𝓙) e z.2 i)
          (incrementsGlobalObservationVector (I := 𝓙) e z.2 j) : ℂ))
      let Rest := fun z : X => actualFiniteMetricError (fun w => F w.1 (e.symm w.2))
        (U ∘ b.symm) (fun _ => 0) delta z-Mean z
      ContDiffOn ℝ ∞ Rest Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
        tau^k*‖iteratedFDeriv ℝ k Rest z‖ ≤ CR*(delta*(tau/ell)^q+delta^3/tau) := by
  obtain ⟨CH,hCH,hFamily⟩ := actual_original_secondary_family_from_raw
    (m := m) (N := N) (Ep := Ep) (M := M) (Tr := Tr) (Label := Label) (SubPrimary := SubPrimary)
    (SubSecondary := SubSecondary) nInput nSolve q Rsub Lprimary hq hInput
    reserve Bnd Mg Kcut hc hBnd hMg hKcut T Tinv hT hTinv
  obtain ⟨CU,CP,hCU,hCP,hPrimary⟩ := actual_original_primary_consumers_from_raw
    (m := m) (N := N) (Ep := Ep) (M := M) (Tr := Tr) (Label := Label) (Sub := SubPrimary)
    nInput (q+2) j Rsub Lprimary (by omega) reserve Bnd Mg hc hBnd hMg T hT
  obtain ⟨MD,hMD,hCoeff⟩ := actual_original_physical_coefficient_profiles_from_raw
    (I := 𝓙) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (Λ := Label) (Β := SubPrimary)
    nInput q j Rsub Lprimary hq (by omega) reserve Bnd Mg hc hBnd hMg T hT
  let CR := actualConstructedFiniteErrorCost m N nSolve j (q+2) Lprimary Rsecondary Mg CH CU CP 0 Tobs
  have hCR : 0 ≤ CR := by
    have hW := actualSecondaryForcedWaveCost_nonneg m N nSolve (q+2) (j+1) Mg CH hMg hCH
    have hP := actualSecondaryPhysicalCost_nonneg m N nSolve (q+2) (j+1) Mg CH hMg hCH
    have hV := actualFastChartTransferPrefix_nonneg Tobs hTobs (j+1)
    have hT0 := actualFastTensorChartTransferPrefix_nonneg Tobs hTobs (j+1)
    dsimp only [CR,actualConstructedFiniteErrorCost,actualConstructedSecondaryWaveBudget,
      actualConstructedSecondaryPhysicalBudget]
    positivity
  refine ⟨CR,hCR,?_⟩
  intro F hF g input inputbar W primary ell delta tau Delta hdelta hdeltatau choice geom hcChoice hChartChoice hPhaseChoice
    hHost hHostInv hHostSource hSupport hPair hPartition host transition cutoff hCut hInv rawHost hcut hinv
    e he heInv Omega S rawObs hTarget hFobs pgeom b hTransition hInverse O hO hOOmega hActive hSource hSample
    hTransitionBound hCount U Mean Rest
  obtain ⟨data,hd,hsum⟩ := hFamily F hF g input inputbar W primary (j+1) ell delta tau Delta choice geom
    hcChoice hChartChoice hPhaseChoice hHost hHostInv hHostSource hSupport hCut hInv rawHost hcut hinv
  have hchart (r) (a) : (data r a).base.chart = (geom r a).chart :=
    (hd r a).2.1.trans (hChartChoice r a).symm
  have hsupp (r) (a) : (data r a).base.support = (geom r a).support := (hd r a).2.2.2.1
  have hsample (r) (a) : (data r a).base.sample = (geom r a).sample := (hd r a).2.2.2.2.1
  let phi := fun nu p x => g.phase nu (p,e.symm x)
  let P := fun nu p beta x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau true nu beta (p,e.symm x)
  let Q := fun nu p beta x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau false nu beta (p,e.symm x)
  let U1 := actualPrimaryJointWave phi tau (fun _ _ _ _ => 1) P Q
  let U2 := actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau (q+2) ∘ b.symm
  have hBind : ∀ r : ActualSecondarySignedRecord Label,
      let H := incrementsSecondaryQuadraticForcing phi tau (fun _ _ _ _ => 1) P Q
        (fun i _ => EuclideanSpace.single i 1) r.val.1.1 r.val.1.2 r.val.2
      ActualSecondaryForcingBinding F hF (fun a => (data r a).base) b
        (fun z => actualRealTensorAssembly (H z)) (fun z => actualImaginaryTensorAssembly (H z))
        (incrementsSecondaryQuadraticPhase phi r.val.1.1 r.val.1.2 r.val.2) := by
    intro r
    exact actual_original_secondary_observer_binding F hF g input W primary rawObs.prim nSolve (j+1) q hq
      ell Mg CH tau delta rawObs.htau r.val (fun a => (data r a).base) (fun a => (choice r a).host)
      (hHost r) (hHostInv r)
      (fun a y hy => (hHostSource r a (by simpa only [hchart] using hy)).2)
      (fun a => (choice r a).cutoff)
      (fun a y hy => by change y.val ∈ (data r a).base.chart.source; rw [hchart]; exact (geom r a).support_source (hSupport r a hy))
      (hPartition r) (fun a => (hd r a).2.2.1)
      (fun a => by simpa only [actualOriginalSecondaryRealForcing,actualOriginalSecondaryQuadratic,(hd r a).2.1]
        using (hd r a).2.2.2.2.2.1)
      (fun a => by simpa only [actualOriginalSecondaryImagForcing,actualOriginalSecondaryQuadratic,(hd r a).2.1]
        using (hd r a).2.2.2.2.2.2)
      e he heInv
      (fun a => by simpa only [hchart] using hTransition r a)
      (fun a => by simpa only [hchart] using hInverse r a)
  have hb : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ b.symm Omega := by
    have hf0 : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ (fun z : X => z.1) Omega := contDiffOn_fst.contMDiffOn
    have hs0 : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞ (fun z : X => z.2) Omega := contDiffOn_snd.contMDiffOn
    exact hf0.prodMk (heInv.comp hs0 (fun z hz => hTarget z hz))
  have hobsB : Omega ⊆ b.target := fun z hz => ⟨Set.mem_univ _,hTarget z hz⟩
  have ht : ∀ r a, ContDiffOn ℝ ∞ ((data r a).base.chart ∘ b.symm) (O r a) := by
    intro r a
    rw [hchart]
    exact (hTransition r a).mono (fun z hz => ⟨hobsB (hOOmega r a hz),hSource r a hz⟩)
  have hbFun : (b.symm : X → Ep × M) = (fun z : X => (z.1,e.symm z.2)) := rfl
  have hp := hPrimary F hF g input inputbar W primary e Omega S tau ell Delta rawObs pgeom delta
  have hw : U1 = fun z : X => delta • incrementsGlobalPrimaryWave F hF g input (q+2) tau (b.symm z) :=
    actual_original_primary_wave_physical_binding F hF g input (q+2) tau delta (fun z : X => (z.1,e.symm z.2))
  have hU1 : ContDiffOn ℝ ∞ U1 Omega := by rw [hw]; exact hp.1
  have hLin : ContDiffOn ℝ ∞ (actualJointMetricLinearization (fun z : X => F z.1 (e.symm z.2)) U1) Omega := by
    rw [hw]; exact hp.2.1
  have hOpp := actual_primary_opposite_mean_contDiffOn phi tau (fun _ _ _ _ => 1) P Q Omega
    (fun nu => (hCoeff F hF g input inputbar W primary e he heInv Omega S tau ell Delta rawObs hTarget delta nu).1)
  have hRem := actual_constructed_metric_error_without_mean_jets F hF nSolve j q (q+2) ell Mg CH delta tau W
    data hSolve (by omega) (rawObs.htau.trans_le rawObs.htaul) rawObs.hell1 rawObs.htau rawObs.htaul hdelta hdeltatau
    hMg hCH rawObs.prim.hW b phi (fun _ _ _ _ => 1) P Q hBind (fun _ => 0)
    (fun nu => incrementsGlobalRelativeSupport W (g.cutoff nu))
    (fun r a => by rw [hsupp]; exact hPair r a) Omega S rawObs.hO rawObs.hSO hobsB hb rawObs.hmapWO (fun _ _ => rfl)
    O hO hOOmega (fun r a => by simpa only [hsupp] using hActive r a)
    (fun r a => by simpa only [hchart] using hSource r a) ht Tobs hTobs
    (fun r a z hz => by simpa only [hchart,hsample] using hSample r a z (by simpa only [hsupp] using hz))
    (fun r a z hz k hk hkj => by simpa only [hchart] using hTransitionBound r a z (by simpa only [hsupp] using hz) k hk hkj)
    Lprimary Rsecondary rawObs.hCount (fun r z hz => by simpa only [hsupp] using hCount r z hz)
    CU CP hCU hCP hFobs hU1 contDiffOn_const hLin
    (by simpa only [Pi.zero_apply,smul_zero,sub_zero] using hOpp)
    (fun z hz i => actual_original_primary_grouped_derivative F hF g input W primary rawObs.prim q hq tau delta
      rawObs.htau e he heInv z (hTarget z hz) (rawObs.hmapWO hz) i)
    (fun k hk z hz => by
      change tau^k*‖iteratedFDeriv ℝ k U1 z‖ ≤ CU*delta*tau
      rw [hw]
      simpa only [hbFun,abs_of_nonneg hdelta] using hp.2.2.1 k hk z hz)
    (fun k hk z hz => by
      change tau^k*‖iteratedFDeriv ℝ k (actualJointMetricLinearization _ U1) z‖ ≤ CP*delta*tau*(tau/ell)^(q+2)
      rw [hw]
      simpa only [hbFun,abs_of_nonneg hdelta] using hp.2.2.2 k hk z hz)
  have hFvalue : (fun z : X => F (b.symm z).1 (b.symm z).2) = (fun z : X => F z.1 (e.symm z.2)) := rfl
  rw [hFvalue] at hRem
  let R0 := fun z => actualFiniteMetricError (fun w : X => F w.1 (e.symm w.2))
    (fun w => U1 w+U2 w) (fun _ => 0) delta z-actualPrimaryOppositeMeanTensor phi tau (fun _ _ _ _ => 1) P Q z
  have hUeq : U ∘ b.symm = fun z => U1 z+U2 z := by
    funext z
    simp only [Function.comp_apply,U,U2,hw,hsum]
  have heq : EqOn Rest R0 Omega := by
    intro z hz
    change actualFiniteMetricError _ (U ∘ b.symm) (fun _ => 0) delta z-Mean z = _
    rw [hUeq]
    have hm := actual_original_primary_opposite_tensor F hF g input W primary rawObs.prim (q+2) tau delta e he heInv
      z (hTarget z hz) (rawObs.hmapWO hz)
    exact congrArg (fun T : Tensor => actualFiniteMetricError (fun w : X => F w.1 (e.symm w.2))
      (fun w => U1 w+U2 w) (fun _ => 0) delta z-T) hm.symm
  have hr0 : ContDiffOn ℝ ∞ R0 Omega := by
    simpa only [R0,U1,U2,b,Pi.zero_apply,smul_zero,sub_zero] using hRem.1
  refine ⟨hr0.congr heq,?_⟩
  intro k hk z hz
  rw [((heq.eventuallyEq_of_mem (rawObs.hO.mem_nhds (rawObs.hSO hz))).iteratedFDeriv ℝ k).eq_of_nhds]
  simpa only [CR,R0,U1,U2,b,Pi.zero_apply,smul_zero,sub_zero] using hRem.2 k hk z hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_raw_metric_remainder
