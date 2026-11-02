import NormalPolar.ActualRepairModelFirstDefectIncrementProfiles

/-! The arbitrary-order raw producer is consumed, then the genuine inverse
parameter charts and original source-first coordinates are differentiated.
The resulting original base-two/order-j and joint C2 bounds belong to the
literal complete U0, with every mixed secondary from the same physical data.
No completed U0 jet or norm estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N p r count : ℕ} {M Tr Λ Β SubSecondary : Type*}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem actualRepairModelFirstDefect_complete_increment_original_norms_uniform
    (n backgroundLength probeLength secondaryLength j Rbackground L Rsecondary : ℕ)
    (hbackgroundOrder : j+3+backgroundLength ≤ n)
    (hprobeOrder : j+3+probeLength ≤ n) (hsecondaryOrder : j+3+secondaryLength ≤ n)
    (reserve Bnd Mg CH Bchi Bnu rho Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hrho : 0 ≤ rho)
    (weight : Fin r → ℝ) (Tbackground Tprobe Tsecondary TP : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k)
    (hTsecondary : ∀ k, 0 ≤ Tsecondary k) (hTP : ∀ k, 0 ≤ TP k) :
    ∃ Cbackground : ℝ, 0 ≤ Cbackground ∧ ∀
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (tau ell delta Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
    (W : Set (Ep × M)) (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n (j+2) ell Mg CH delta W)
    (hprimary : ∀ rec q, (data rec q).base.support ⊆ K rec.val.1.1 ∩ K rec.val.1.2)
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph Ep Ep)
    (hB : ∀ b, B b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (profiles : ActualRepairModelFirstDefectIncrementProfiles (Tr := Tr) F hF g c chi nu phase a input inputbar
      n backgroundLength j Rbackground L Rsecondary reserve Bnd Mg CH Bchi Bnu Mphase tau ell delta Delta
      Tbackground Tprobe Tsecondary W K data A B S)
    (hParam : ∀ i : Fin A.count × Fin count, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k → k ≤ j+2 →
      ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k)
    (u : Fin p → ℝ) (hu : ‖u‖ ≤ rho),
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let CR := actualPrescribedRawAmplitudeCost m N n probeLength (j+2) Tprobe weight Mg Bchi Bnu rho false
    let CI := actualPrescribedRawAmplitudeCost m N n probeLength (j+2) Tprobe weight Mg Bchi Bnu rho true
    let Cprobe := actualFinitePrimaryJetConstant L N (j+2) Mphase CR CI
    let Csecondary := actualConstructedSecondaryWaveBudget m N n (j+2) secondaryLength L Rsecondary Mg CH Tsecondary
    let Bcost := Cbackground+Cprobe+Csecondary
    let C := actualRepairModelFirstDefectMapNormCost m d N j (actualFastChartTransferPrefix TP (j+2)*Bcost)
    let U₀ := actualProbeCompleteFirstIncrement F hF g label c vf phase backgroundLength probeLength
      a input u data tau secondaryLength
    let coordinates := incrementsOriginalMapCoordinates A B U₀
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 2 j tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 2 j tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta/tau) ∧
    (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta/tau) := by
  obtain ⟨Cbackground,hCbackground,hraw⟩ := actual_complete_first_increment_raw_weighted_jets_uniform
    (M := M) («Ep» := Ep) (Tr := Tr) (m := m) (N := N) (p := p) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    n backgroundLength probeLength secondaryLength (j+1) Rbackground L Rsecondary
    (by omega) (by omega) (by omega) reserve Bnd Mg CH Bchi Bnu rho Mphase
    hreserve hBnd hMg hCH hBchi hBnu hrho weight Tbackground Tprobe Tsecondary hTbackground hTprobe hTsecondary
  refine ⟨Cbackground,hCbackground,?_⟩
  intro F hF g label c chi nu phase a input inputbar tau ell delta Delta htau htaul hell1 hdelta hdeltatau
    W K data hprimary A B hB S hSO profiles hParam u hu vf CR CI Cprobe Csecondary Bcost C U₀ coordinates
  have hBcost : 0 ≤ Bcost := by
    have hR := actualPrescribedRawAmplitudeCost_nonneg m N n probeLength (j+2) Tprobe weight Mg Bchi Bnu rho false
      hTprobe hMg hBchi hBnu hrho
    have hI := actualPrescribedRawAmplitudeCost_nonneg m N n probeLength (j+2) Tprobe weight Mg Bchi Bnu rho true
      hTprobe hMg hBchi hBnu hrho
    have hP := actualFinitePrimaryJetConstant_nonneg L N (j+2) Mphase hR hI
    have hS := actualSecondaryForcedWaveCost_nonneg m N n secondaryLength (j+2) Mg CH hMg hCH
    have hT := actualFastChartTransferPrefix_nonneg Tsecondary hTsecondary (j+2)
    dsimp only [Bcost,Cprobe,Csecondary,actualConstructedSecondaryWaveBudget]
    positivity
  have hjoint (i : Fin A.count × Fin count) :
      ContDiffOn ℝ ∞ (fun z : X => U₀ (z.1,(A.chart i.1).symm z.2)) (profiles.domains i) ∧
      ∀ k ≤ j+2, ∀ z ∈ parameterRound2_meanParameterMap (m := m) (B i.2) ''
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i),
        tau^k*‖iteratedFDeriv ℝ k (fun z : X => U₀ (z.1,(A.chart i.1).symm z.2)) z‖ ≤ Bcost*delta*tau :=
    hraw F hF g label c chi nu phase a input inputbar tau ell delta Delta hdelta hdeltatau W K
      (A.chart i.1) (profiles.domains i) (parameterRound2_meanParameterMap (m := m) (B i.2) ''
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) (profiles.background i) profiles.adaptation
      (profiles.observer_smooth i) (profiles.prescribed i) data hprimary (profiles.secondary i) u hu
  exact actualRepairModelFirstDefect_map_norms_after_parameter_charts A B hB S hSO U₀ j tau ell delta Bcost
    htau htaul hell1 hdelta hBcost TP hTP profiles.domains (fun i => (profiles.background i).hO)
    (fun i => (profiles.background i).hSO) (fun i => (hjoint i).1) (fun i => (hjoint i).2) hParam

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_complete_increment_original_norms_uniform
