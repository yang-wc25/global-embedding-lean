import NormalPolar.JointSecondaryCarrierFamilyBinding
import NormalPolar.JointMixedGroupedPrimaryJets
import NormalPolar.JointMixedGroupedPrimaryPhysical
import NormalPolar.JointSecondaryGroupedRegularity
import NormalPolar.JointMixedGroupedRemainderJets
import NormalPolar.JointMixedNativeObservation
import NormalPolar.JointMixedRemainderJets
import NormalPolar.JointMixedPrimaryPhysical
import NormalPolar.JointSecondaryRegularity
import NormalPolar.ActualProbeInitialSupplyPrimary

/-! Independent open primitive domains and true amplitude carriers.
The full literal joint primary-plus-secondary metric remainder from raw
profiles on a genuine native chart.  CH, M1 and CP are all constructed before
the maps, scales and parameter field are supplied.  The conclusion uses the
explicit physical secondary source, so it is independent of the chosen
certificates for its finite raw pieces.  Every parameter derivative is taken
after substitution into that one family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)] {Ep M Tr Λ Β Sub : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord (Λ ⊕ Fin r)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

private local instance rawNativeTensorSemi : SeminormedAddCommGroup
    ((EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance rawNativeTensorNormed : NormedAddCommGroup
    ((EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance rawNativeTensorSpace : NormedSpace ℝ
    ((EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem actualProbeInitialSupply_carrier_native_remainder_from_raw_uniform
    (nInput nSolve q probeLength j length Rbackground L Rprobe Rsecondary : ℕ)
    (hq : 1 ≤ q) (hbackgroundOrder : nSolve+2+(q+2) ≤ nInput)
    (hprobeOrder : nSolve+2+probeLength ≤ nInput)
    (hbudget : j+2+length ≤ nSolve) (hql : q ≤ length)
    (hlengthBackground : length ≤ q+2) (hlengthProbe : length ≤ probeLength)
    (hLcard : Fintype.card (Λ ⊕ Fin r) ≤ L)
    (reserve Bnd Mg Kcut Bchi Bnu Ku Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku) (hMphase : 0 ≤ Mphase)
    (weight : Fin r → ℝ) (hweight : ∀ l, weight l ≠ 0)
    (Tbackground Tprobe Tinv Tobs : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : (l : Fin r) → Pieces l → Ep → D → M) (chi : (l : Fin r) → Pieces l → X → ℝ)
    (nu : (l : Fin r) → (s : Pieces l) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (Ep × M) X) (phase : Fin r → Ep × M → ℝ)
    (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : Ep → Fin p → ℝ) (tau ell delta Delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
    (W : Set (Ep × M)) (primaryDomain : Λ → Set (Ep × M))
    (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (pieceK : (l : Fin r) → Pieces l → Set (Ep × M))
    (profiles : JointGroupedSecondaryCarrierProfiles (Sub := Sub) (Tr := Tr) F hF g c chi nu a phase
      input inputbar u W primaryDomain K pieceK nInput nSolve q probeLength (j+1) Rbackground L
      reserve Bnd Mg Kcut Bchi Bnu Ku Mphase tau ell delta Delta Tbackground Tprobe Tinv)
    (e : OpenPartialHomeomorph M D) (Omega S : Set X)
    (observer : JointMixedNativeObserverGeometry F hF nSolve j ell Mg W
      profiles.geometry e Omega S K L Rsecondary Tobs)
    (background : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) j Rbackground L
      reserve Bnd Mg Tbackground F hF g input inputbar W primaryDomain e Omega S tau ell Delta)
    (backgroundGeometry : ActualOriginalPrimaryPhysicalGeometry F hF g)
    (prescribed : JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK
      nInput (j+1) ell Mg Bchi Bnu (fun z : X => (z.1,e.symm z.2)) Omega S Tprobe phase Mphase)
    (prescribedGeometry : ∀ l s, ActualPrescribedPhysicalGeometry F hF (c l s) (nu l s) (a l s) (phase l))
    (hRprobe : ∀ l y, y ∈ S → (Finset.univ.filter (fun s => (y.1,e.symm y.2) ∈ pieceK l s)).card ≤ Rprobe)
    (hu : ContDiffOn ℝ ∞ (fun z : X => u z.1) Omega)
    (hub : ∀ k ≤ j+1, ∀ z ∈ S,
      ell^k*‖iteratedFDeriv ℝ k (fun y : X => u y.1) z‖ ≤ Ku),
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let phases := Sum.elim g.phase phase
    let R := jointGroupedCombinedAmplitude F hF g label c vf tau delta (q+2) probeLength a input u false
    let Q := jointGroupedCombinedAmplitude F hF g label c vf tau delta (q+2) probeLength a input u true
    let source := fun rec s => jointSecondarySourceOfRawGeometry F hF nSolve (j+1) ell Mg W
      (profiles.geometry rec s) (profiles.host rec s) (profiles.cutoff rec s) phases R Q tau rec.val
    let kappa := fun z : X => (z.1,e.symm z.2)
    let Fobs := fun z : X => F z.1 (e.symm z.2)
    let U1 := fun z : X => jointGroupedCombinedPrimary F hF g label c vf phase tau delta
      (q+2) probeLength a input (u z.1) (kappa z)
    let U2 := actualParameterSecondarySourceSum F hF source tau length ∘ kappa
    let Mean := actualPrimaryOppositeMeanTensor (fun l b x => phases l (b,e.symm x)) tau
      (fun (_ : Λ ⊕ Fin r) (_ : Ep) (_ : Unit) (_ : D) => (1 : ℝ))
      (fun l b (_ : Unit) x => R l (b,e.symm x)) (fun l b (_ : Unit) x => Q l (b,e.symm x))
    let rest := fun z => actualFiniteMetricError Fobs (fun y => U1 y+U2 y) (fun _ => 0) delta z - Mean z
    ContDiffOn ℝ ∞ rest Omega ∧
      ∀ k ≤ j, ∀ z ∈ S, tau^k*‖iteratedFDeriv ℝ k rest z‖ ≤
        C*(delta*(tau/ell)^q+delta^3/tau) := by
  obtain ⟨CH,hCH,hfamily⟩ := jointCarrier_mixed_family_from_raw_uniform
    (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (p := p) (Λ := Λ) (Β := Β) (Pieces := Pieces) (Sub := Sub)
    nInput nSolve q probeLength Rbackground L hq hbackgroundOrder hprobeOrder
    reserve Bnd Mg Kcut Bchi Bnu Ku Mphase hreserve hBnd hMg hKcut hBchi hBnu hKu hMphase
    weight Tbackground Tprobe Tinv hTbackground hTprobe hTinv
  obtain ⟨M1,hM1,hjets⟩ := jointGrouped_primary_raw_jets_uniform
    (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (p := p) (Λ := Λ) (Β := Β) (Pieces := Pieces)
    nInput (q+2) probeLength j Rbackground L Rprobe (by omega) (by omega)
    reserve Bnd Mg Bchi Bnu Ku Mphase hreserve hBnd hMg hBchi hBnu hKu weight
    Tbackground Tprobe hTbackground hTprobe
  obtain ⟨CP,hCP,hphysical⟩ := jointGrouped_combined_primary_raw_physical_uniform
    (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (p := p) (Λ := Λ) (Β := Β) (Pieces := Pieces)
    nInput (q+2) probeLength j length Rbackground L Rprobe (by omega) (by omega)
    hlengthBackground hlengthProbe reserve Bnd Mg Bchi Bnu Ku Mphase hreserve hBnd hMg hBchi hBnu hKu
    weight hweight Tbackground Tprobe hTbackground hTprobe
  let C0 := actualConstructedFiniteErrorCost m N nSolve j length L Rsecondary Mg CH M1 CP 0 Tobs
  refine ⟨max C0 0,le_max_right _ _,?_⟩
  intro F hF g label c chi nu a phase input inputbar u tau ell delta Delta hdelta hdeltatau W primaryDomain K pieceK
    profiles e Omega S observer background backgroundGeometry prescribed prescribedGeometry hRprobe hu hub
    vf phases R Q source kappa Fobs U1 U2 Mean rest
  obtain ⟨data,spec⟩ := hfamily F hF g label c chi nu a phase input inputbar u tau ell delta Delta
    hdelta W primaryDomain K pieceK (j+1) profiles
  let Kopen : (Λ ⊕ Fin r) → Set (Ep × M) :=
    Sum.elim primaryDomain (fun l => K (Sum.inr l))
  have hCountOpen : ∀ y ∈ S,
      (Finset.univ.filter (fun l => (y.1,e.symm y.2) ∈ Kopen l)).card ≤ L := by
    intro y hy
    exact ((Finset.card_filter_le _ _).trans_eq (by simp)).trans hLcard
  have hj := hjets F hF g label c chi nu phase a input inputbar tau ell delta Delta hdelta W Kopen pieceK profiles.piece_support
    e Omega S background backgroundGeometry.adaptation prescribed hCountOpen hRprobe u hu hub
  have hp := hphysical F hF g label c chi nu phase a input inputbar tau ell delta Delta hdelta W Kopen pieceK profiles.piece_support
    e Omega S background backgroundGeometry prescribed prescribedGeometry hCountOpen hRprobe u hu
    (fun k hk z hz => hub k (by omega) z hz)
  have hkappa : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod IM) ∞ kappa Omega := by
    have hf : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ (fun z : X => z.1) Omega := contDiffOn_fst.contMDiffOn
    have hs : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,D) ∞ (fun z : X => z.2) Omega := contDiffOn_snd.contMDiffOn
    exact hf.prodMk ((contMDiffOn_symm_of_mem_maximalAtlas observer.host_maximal).comp hs observer.target)
  have hr := jointGrouped_common_regular_from_primitives F hF g label c chi nu phase a input W Kopen pieceK
    background.prim nInput (j+1) (q+2) probeLength ell Mg Bchi Bnu tau delta weight kappa Omega S
    background.hO hkappa background.hmapWO Tprobe Mphase prescribed u hu
  have hc (rec : Rec) (s : Sub) : (data rec s).base.chart = (profiles.geometry rec s).chart :=
    (spec rec s).2.1
  have hs (rec : Rec) (s : Sub) : (data rec s).base.support = (profiles.geometry rec s).support :=
    (spec rec s).2.2.2.1
  have hz (rec : Rec) (s : Sub) : (data rec s).base.sample = (profiles.geometry rec s).sample :=
    (spec rec s).2.2.2.2.1
  have hbfun : ⇑((OpenPartialHomeomorph.refl Ep).prod e).symm = kappa := rfl
  have hbinding := jointCarrier_family_observer_binding_from_primitives F hF g label c chi nu a phase
    input inputbar u W primaryDomain K pieceK nInput nSolve q probeLength (j+1) Rbackground L
    reserve Bnd Mg Kcut Bchi Bnu Ku Mphase tau ell delta Delta CH Tbackground Tprobe Tinv
    profiles background.prim nInput (j+1) prescribed.raw weight data spec e observer.host_maximal
    (fun rec s => by rw [hc]; exact observer.transition_smooth rec s)
    (fun rec s => by rw [hc]; exact observer.inverse_smooth rec s)
  have hn := jointGrouped_combined_remainder_jets F hF g label c vf phase (q+2) probeLength a input u
    nSolve j q length ell Mg CH delta tau W data hbudget hql
    (background.htau.trans_le background.htaul) background.hell1 background.htau background.htaul
    hdelta hdeltatau hMg hCH background.prim.hW ((OpenPartialHomeomorph.refl Ep).prod e)
    hbinding (fun _ => 0) K
    (fun rec s => by rw [hs]; exact observer.primary_support rec s)
    Omega S background.hO background.hSO
    (fun z hz => ⟨mem_univ _,observer.target z hz⟩) hkappa background.hmapWO (fun _ _ => rfl)
    observer.localDomain observer.local_open observer.local_subset
    (fun rec s => by rw [hs]; exact observer.active_local rec s)
    (fun rec s => by rw [hc]; exact observer.source rec s)
    (fun rec s => by
      rw [hc,hbfun]
      exact JointMixedNativeObserverGeometry.local_transition_smooth F hF nSolve j ell Mg W
        profiles.geometry e Omega S K L Rsecondary Tobs observer rec s)
    Tobs hTobs
    (fun rec s z h => by
      rw [hc,hz,hbfun]
      exact observer.active_sample rec s z (by simpa only [hs,hbfun] using h))
    (fun rec s z h k hk hk' => by
      rw [hc,hbfun]
      exact observer.transition_bound rec s z (by simpa only [hs,hbfun] using h) k hk hk')
    L Rsecondary observer.primary_count
    (fun rec z hz => by simpa only [hs,hbfun] using observer.secondary_count rec z hz)
    M1 CP hM1 hCP observer.ambient_smooth hj.1 contDiffOn_const hp.2.1
    (by simpa only [smul_zero,sub_zero,hbfun] using hr.2.1) hr.2.2 hj.2 hp.2.2
  have he := jointSecondary_sum_eq_physical_source F hF nSolve (j+1) ell Mg CH delta W
    profiles.geometry profiles.host profiles.cutoff phases R Q tau data spec tau length
  dsimp only at hn
  rw [he] at hn
  have hout : ContDiffOn ℝ ∞ rest Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
      tau^k*‖iteratedFDeriv ℝ k rest z‖ ≤ C0*(delta*(tau/ell)^q+delta^3/tau) := by
    simpa only [smul_zero,sub_zero,hbfun,kappa] using hn
  refine ⟨hout.1,?_⟩
  intro k hk z hzs
  apply (hout.2 k hk z hzs).trans
  exact mul_le_mul_of_nonneg_right (le_max_left C0 0)
    (by have htau := background.htau; have hell := background.htau.trans_le background.htaul; positivity)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_carrier_native_remainder_from_raw_uniform
