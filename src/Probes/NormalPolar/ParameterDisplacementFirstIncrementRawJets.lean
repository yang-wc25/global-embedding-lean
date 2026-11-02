import NormalPolar.ParameterDisplacementPrescribedWave
import NormalPolar.ParameterDisplacementFirstIncrementJets
import Probes.ActualIncrementRawPrimaryWave

/-!
# Arbitrary-order joint jets of the literal complete first increment

The background uses its actual raw mean packet. The prescribed two-channel
wave is reconstructed from its primitive normal source. Every signed mixed
secondary is obtained from the same physical piece data. Thus no completed
primary, secondary, or U0 jet budget is an assumption. The order is arbitrary;
in particular these are joint jets, not just fixed-parameter spatial jets.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {Ep M Tr Λ Β SubSecondary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

/-- Genuine geometry of all actual secondary observations; no output jet
appears among the fields. -/
structure ActualSecondaryRawObservationProfiles
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (kappa : Y → Ep × M) (Omega S : Set Y)
    (K : (Λ ⊕ Fin r) → Set (Ep × M)) (T : ℕ → ℝ) (L R : ℕ) where
  domains : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary → Set Y
  domains_open : ∀ rec q, IsOpen (domains rec q)
  active_domain : ∀ rec q, S ∩ kappa ⁻¹' (data rec q).base.support ⊆ domains rec q
  source : ∀ rec q, MapsTo kappa (domains rec q) (data rec q).base.chart.source
  transition_smooth : ∀ rec q, ContDiffOn ℝ ∞ ((data rec q).base.chart ∘ kappa) (domains rec q)
  sample : ∀ rec q y, y ∈ S ∩ kappa ⁻¹' (data rec q).base.support →
    (data rec q).base.chart (kappa y) ∈ (data rec q).base.sample
  transition_jets : ∀ rec q y, y ∈ S ∩ kappa ⁻¹' (data rec q).base.support →
    ∀ k, 1 ≤ k → k ≤ j → ell^(k-1)*‖iteratedFDeriv ℝ k ((data rec q).base.chart ∘ kappa) y‖ ≤ T k
  primary_count : ∀ y ∈ S, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ L
  secondary_count : ∀ rec y, y ∈ S →
    (Finset.univ.filter (fun q => kappa y ∈ (data rec q).base.support)).card ≤ R

/-- The joint U0 bound is produced uniformly before its scales, maps, and
probe parameter. Both true primitive packets and the physical secondary
array are consumed at their original domains. -/
theorem actual_complete_first_increment_raw_weighted_jets_uniform
    (n backgroundLength probeLength secondaryLength j Rbackground L Rsecondary : ℕ)
    (hbackgroundOrder : j+2+backgroundLength ≤ n)
    (hprobeOrder : j+2+probeLength ≤ n) (hsecondaryOrder : j+2+secondaryLength ≤ n)
    (reserve Bnd Mg CH Bchi Bnu rho Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hrho : 0 ≤ rho)
    (weight : Fin r → ℝ) (Tbackground Tprobe Tsecondary : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k)
    (hTsecondary : ∀ k, 0 ≤ Tsecondary k) :
    ∃ Cbackground : ℝ, 0 ≤ Cbackground ∧ ∀
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (tau ell delta Delta : ℝ) (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
    (W : Set (Ep × M)) (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (e : OpenPartialHomeomorph M D) (Omega S : Set X)
    (background : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n backgroundLength j Rbackground L
      reserve Bnd Mg Tbackground F hF g input inputbar W (fun l => K (Sum.inl l)) e Omega S tau ell Delta)
    (hadapt : ∀ l q z, z ∈ (g.chart l q).source → g.phase l z = (g.chart l q z).2 0)
    (hkappa : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod IM) ∞
      (fun z : X => (z.1,e.symm z.2)) Omega)
    (prescribed : ActualPrescribedObservationProfiles F hF c chi nu a W (fun l => K (Sum.inr l))
      n (j+1) ell Mg Bchi Bnu (fun z : X => (z.1,e.symm z.2)) Omega S Tprobe phase Mphase)
    (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n (j+1) ell Mg CH delta W)
    (hprimary : ∀ rec q, (data rec q).base.support ⊆ K rec.val.1.1 ∩ K rec.val.1.2)
    (secondary : ActualSecondaryRawObservationProfiles F hF n (j+1) ell Mg CH delta W data
      (fun z : X => (z.1,e.symm z.2)) Omega S K Tsecondary L Rsecondary)
    (u : Fin p → ℝ) (hu : ‖u‖ ≤ rho),
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let CR := actualPrescribedRawAmplitudeCost m N n probeLength (j+1) Tprobe weight Mg Bchi Bnu rho false
    let CI := actualPrescribedRawAmplitudeCost m N n probeLength (j+1) Tprobe weight Mg Bchi Bnu rho true
    let Cprobe := actualFinitePrimaryJetConstant L N (j+1) Mphase CR CI
    let Csecondary := actualConstructedSecondaryWaveBudget m N n (j+1) secondaryLength L Rsecondary Mg CH Tsecondary
    let B := Cbackground + Cprobe + Csecondary
    let U := actualProbeCompleteFirstIncrement F hF g label c vf phase backgroundLength probeLength
      a input u data tau secondaryLength ∘ (fun z : X => (z.1,e.symm z.2))
    ContDiffOn ℝ ∞ U Omega ∧ ∀ k ≤ j+1, ∀ y ∈ S,
      tau^k*‖iteratedFDeriv ℝ k U y‖ ≤ B*delta*tau := by
  obtain ⟨Cbackground,hCbackground,hbackground⟩ := actual_original_primary_wave_from_raw_uniform
    (I := IM) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (Λ := Λ) (Β := Β)
    n backgroundLength j Rbackground L hbackgroundOrder reserve Bnd Mg hreserve hBnd hMg Tbackground hTbackground
  refine ⟨Cbackground,hCbackground,?_⟩
  intro F hF g label c chi nu phase a input inputbar tau ell delta Delta hdelta hdeltatau
    W K e Omega S background hadapt hkappa prescribed data hprimary secondary u hu
    vf CR CI Cprobe Csecondary B U
  let kappa := fun z : X => (z.1,e.symm z.2)
  have htau := background.htau
  have hell : 0 < ell := htau.trans_le background.htaul
  have hCsecondary : 0 ≤ Csecondary := by
    have hc := actualSecondaryForcedWaveCost_nonneg m N n secondaryLength (j+1) Mg CH hMg hCH
    have hp := actualFastChartTransferPrefix_nonneg Tsecondary hTsecondary (j+1)
    dsimp only [Csecondary,actualConstructedSecondaryWaveBudget]
    positivity
  have hLprobe (y : X) (hy : y ∈ S) :
      (Finset.univ.filter (fun l : Fin r => kappa y ∈ K (Sum.inr l))).card ≤ L := by
    apply (Finset.card_le_card_of_injOn (Sum.inr : Fin r → Λ ⊕ Fin r) ?_ ?_).trans (secondary.primary_count y hy)
    · intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    · intro l _ q _ h
      exact Sum.inr.inj h
  let bg := fun z : X => delta • incrementsGlobalPrimaryWave F hF g input backgroundLength tau (kappa z)
  let pr := round4PrescribedGlobalWave label F hF c vf phase tau probeLength a u ∘ kappa
  let sec := actualConstructedSecondarySum F hF (fun rec q => (data rec q).base) tau secondaryLength ∘ kappa
  have hb := hbackground F hF g input inputbar W (fun l => K (Sum.inl l)) e Omega S tau ell Delta background hadapt
  have hbg : ContDiffOn ℝ ∞ bg Omega := hb.1.const_smul delta
  have hpr := actual_prescribed_wave_from_raw label F hF c chi nu a W (fun l => K (Sum.inr l))
    background.prim.hW n probeLength (j+1) (by omega) tau ell delta weight Mg Bchi Bnu rho
    htau background.htaul background.hell1 hMg hdelta hBchi hBnu hrho
    kappa Omega S background.hO background.hSO background.hkappaO background.hmapWO
    Tprobe hTprobe phase Mphase prescribed L hLprobe u hu
  have hsec : ContDiffOn ℝ ∞ sec Omega := actual_secondary_sum_arbitrary_observation_smooth
    F hF data tau secondaryLength background.prim.hW kappa Omega hkappa background.hmapWO
  have hs := actual_constructed_secondary_sum_weighted_jets F hF (fun rec q => (data rec q).base)
    tau secondaryLength (by omega) hell background.hell1 htau background.htaul hMg hCH
    background.prim.hW K hprimary kappa Omega S background.hO background.hSO
    background.hkappaO background.hmapWO secondary.domains secondary.domains_open secondary.active_domain
    secondary.source secondary.transition_smooth Tsecondary hTsecondary secondary.sample
    secondary.transition_jets L Rsecondary secondary.primary_count secondary.secondary_count
  have heq : U = fun z => (bg z + pr z) + sec z := by
    funext z
    dsimp only [U,actualProbeCompleteFirstIncrement,Function.comp_def,bg,pr,sec,kappa]
    rw [round4ParameterProbeCombinedPrimary_eq]
  rw [heq]
  refine ⟨(hbg.add hpr.1).add hsec,?_⟩
  intro k hk y hy
  have hmem := background.hO.mem_nhds (background.hSO hy)
  have hbgj : tau^k*‖iteratedFDeriv ℝ k bg y‖ ≤ Cbackground*delta*tau := by
    simpa only [abs_of_nonneg hdelta] using hb.2 delta k hk y hy
  have hfirst := actual_joint_slow_add_jet_bound bg pr k tau (Cbackground*delta*tau) (Cprobe*delta*tau)
    htau.le y ((hbg.contDiffAt hmem).of_le (by simp)) ((hpr.1.contDiffAt hmem).of_le (by simp))
    hbgj (hpr.2 k hk y hy)
  have htotal := actual_joint_slow_add_jet_bound (fun z => bg z+pr z) sec k tau
    (Cbackground*delta*tau+Cprobe*delta*tau) (Csecondary*delta^2) htau.le y
    (((hbg.add hpr.1).contDiffAt hmem).of_le (by simp)) ((hsec.contDiffAt hmem).of_le (by simp))
    hfirst (hs.2 k hk y hy)
  apply htotal.trans
  have hmul := mul_le_mul_of_nonneg_left hdeltatau hdelta
  have habs := mul_le_mul_of_nonneg_left hmul hCsecondary
  change _ ≤ (Cbackground+Cprobe+Csecondary)*delta*tau
  nlinarith

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_complete_first_increment_raw_weighted_jets_uniform
