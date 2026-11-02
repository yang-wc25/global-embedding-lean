import NormalPolar.JointSecondaryCarrierFamilyBinding
import NormalPolar.JointMixedGroupedPrimaryJets
import NormalPolar.JointMixedNativeObservation
import NormalPolar.JointSecondarySupport
import Probes.ActualSecondaryCompleteMetricJets
import NormalPolar.ActualProbeInitialSupplyPrimary

/-! Independent open primitive domains and true amplitude carriers.
The same literal joint primary-plus-secondary displacement and its
native jets, from raw profiles.  The geometry/source fields are identical
to the raw full-remainder construction, through the same j+1 derivatives.
The complete secondary sum is estimated directly from its finite pieces,
without introducing a second global parameter atlas or another witness. -/

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

theorem actualProbeInitialSupply_carrier_native_increment_from_raw_uniform
    (nInput nSolve q probeLength j length Rbackground L Rprobe Rsecondary : ℕ)
    (hq : 1 ≤ q) (hbackgroundOrder : nSolve+2+(q+2) ≤ nInput)
    (hprobeOrder : nSolve+2+probeLength ≤ nInput)
    (hbudget : j+2+length ≤ nSolve)
    (hLcard : Fintype.card (Λ ⊕ Fin r) ≤ L)
    (reserve Bnd Mg Kcut Bchi Bnu Ku Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku) (hMphase : 0 ≤ Mphase)
    (weight : Fin r → ℝ)
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
    let U1 := fun z : X => jointGroupedCombinedPrimary F hF g label c vf phase tau delta
      (q+2) probeLength a input (u z.1) (kappa z)
    let U2 := actualParameterSecondarySourceSum F hF source tau length ∘ kappa
    let increment := fun z => U1 z+U2 z
    ContDiffOn ℝ ∞ increment Omega ∧
      ∀ k ≤ j+1, ∀ z ∈ S, tau^k*‖iteratedFDeriv ℝ k increment z‖ ≤ C*delta*tau := by
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
  let M2 := actualConstructedSecondaryWaveBudget m N nSolve (j+1) length L Rsecondary Mg CH Tobs
  have hM2 : 0 ≤ M2 := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (actualFastChartTransferPrefix_nonneg Tobs hTobs (j+1)))
    (actualSecondaryForcedWaveCost_nonneg m N nSolve length (j+1) Mg CH hMg hCH)
  refine ⟨M1+M2,add_nonneg hM1 hM2,?_⟩
  intro F hF g label c chi nu a phase input inputbar u tau ell delta Delta hdelta hdeltatau W primaryDomain K pieceK
    profiles e Omega S observer background backgroundGeometry prescribed hRprobe hu hub
    vf phases R Q source kappa U1 U2 increment
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
  have hkappa : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod IM) ∞ kappa Omega := by
    have hf : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ (fun z : X => z.1) Omega := contDiffOn_fst.contMDiffOn
    have hs : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,D) ∞ (fun z : X => z.2) Omega := contDiffOn_snd.contMDiffOn
    exact hf.prodMk ((contMDiffOn_symm_of_mem_maximalAtlas observer.host_maximal).comp hs observer.target)
  have hc (rec : Rec) (s : Sub) : (data rec s).base.chart = (profiles.geometry rec s).chart :=
    (spec rec s).2.1
  have hs (rec : Rec) (s : Sub) : (data rec s).base.support = (profiles.geometry rec s).support :=
    (spec rec s).2.2.2.1
  have hz (rec : Rec) (s : Sub) : (data rec s).base.sample = (profiles.geometry rec s).sample :=
    (spec rec s).2.2.2.2.1
  have hsecondary := actual_constructed_secondary_sum_weighted_jets F hF (fun rec s => (data rec s).base)
    tau length (by omega) (background.htau.trans_le background.htaul) background.hell1
    background.htau background.htaul hMg hCH background.prim.hW K
    (fun rec s => by rw [hs]; exact observer.primary_support rec s)
    kappa Omega S background.hO background.hSO background.hkappaO background.hmapWO
    observer.localDomain observer.local_open
    (fun rec s => by rw [hs]; exact observer.active_local rec s)
    (fun rec s => by rw [hc]; exact observer.source rec s)
    (fun rec s => by
      rw [hc]
      exact JointMixedNativeObserverGeometry.local_transition_smooth F hF nSolve j ell Mg W
        profiles.geometry e Omega S K L Rsecondary Tobs observer rec s)
    Tobs hTobs
    (fun rec s z h => by
      rw [hc,hz]
      exact observer.active_sample rec s z (by simpa only [hs] using h))
    (fun rec s z h k hk hk' => by
      rw [hc]
      exact observer.transition_bound rec s z (by simpa only [hs] using h) k hk (by omega))
    L Rsecondary observer.primary_count
    (fun rec z hz => by simpa only [hs] using observer.secondary_count rec z hz)
  have he := jointSecondary_sum_eq_physical_source F hF nSolve (j+1) ell Mg CH delta W
    profiles.geometry profiles.host profiles.cutoff phases R Q tau data spec tau length
  rw [he] at hsecondary
  have hU2jet : ∀ k ≤ j+1, ∀ z ∈ S,
      tau^k*‖iteratedFDeriv ℝ k U2 z‖ ≤ M2*delta^2 := hsecondary.2
  have hglobal := jointSecondary_physical_source_regular_support F hF nSolve (j+1) ell Mg CH delta W
    profiles.geometry profiles.host profiles.cutoff phases R Q tau data spec background.prim.hW
    univ (fun _ _ => subset_univ _) tau length
  have hU2 : ContDiffOn ℝ ∞ U2 Omega :=
    (hglobal.1.comp hkappa background.hmapWO).contDiffOn
  refine ⟨hj.1.add hU2,?_⟩
  intro k hk z hzs
  have hdeltaScale : delta^2 ≤ delta*tau := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hdeltatau hdelta
  have hbound2 : tau^k*‖iteratedFDeriv ℝ k U2 z‖ ≤ M2*delta*tau :=
    (hU2jet k hk z hzs).trans ((mul_le_mul_of_nonneg_left hdeltaScale hM2).trans_eq (by ring))
  have hmem := background.hO.mem_nhds (background.hSO hzs)
  have hsum := actual_joint_slow_add_jet_bound U1 U2 k tau (M1*delta*tau) (M2*delta*tau)
    background.htau.le z ((hj.1.contDiffAt hmem).of_le (by simp))
    ((hU2.contDiffAt hmem).of_le (by simp)) (hj.2 k hk z hzs) hbound2
  exact hsum.trans_eq (by ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_carrier_native_increment_from_raw_uniform
