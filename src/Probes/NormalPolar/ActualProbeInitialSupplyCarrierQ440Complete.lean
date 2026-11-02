import NormalPolar.JointBackgroundGroupedQ440PhysicalResidual
import NormalPolar.ActualProbeInitialSupplyCarrierRemainder
import NormalPolar.ActualProbeInitialSupplyAssembly

/-! The complete q=440 first increment and metric error from actual raw
inputs on the original parameter manifold. The recurrence constants and cap stay fixed. Separate scalarized first-wave
primitive costs are then fixed before the target, ell, tau or delta. In
particular rehosting does not require a primitive budget to bound its own
amplification, and the same literal u may use its actual first-wave jet cost. The given
raw atlas is for the literal global background after 441 actual iterations;
the source is shared by the map, remainder and original first family.
No completed mean/error, first-state estimate, closed state or run is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
universe uM uTr uP uΛ uΒ
variable {m N d r : ℕ} {M : Type uM} {Tr : Type uTr} {P : Type uP}
  {Λ : Type uΛ} {Β : Type uΒ} {Sub : Type*}
  {Pieces : Fin r → Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [T2Space P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype Sub] [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))
local notation "𝓙" => 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))

attribute [local irreducible] OpenPartialHomeomorph.symm
set_option backward.isDefEq.respectTransparency true in
/-- Transparent statement of the full original-norm conclusion; its raw inputs are explicit. -/
abbrev actualProbeInitialCarrierQ440RawStatement
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (S : Fin A.count × Fin B.count → Set (Fin (m+1+d) → ℝ))
    (hS : ∀ idx, IsCompact (S idx))
    (hSO : ∀ idx, S idx ⊆ incrementsOriginalDifferentiation A B.chart idx)
    (hSQ : ∀ idx z, parameterTensorModelEquiv (m+1) d z ∈ S idx → z.1 ∈ Q idx.2)
    (Tp : ℕ → ℕ → ℝ) (hTp : ∀ j k, 0 ≤ Tp j k)
    (weight : Fin r → ℝ) (hweight : ∀ l, weight l ≠ 0) (Mgp Bchi Bnu Mphase : ℕ → ℝ)
    (hMgp : ∀ j, 0 ≤ Mgp j) (hBchi : ∀ j, 0 ≤ Bchi j)
    (hBnu : ∀ j, 0 ≤ Bnu j) (hMphase : ∀ j, 0 ≤ Mphase j)
    (rho : ℝ) (hrho : 0 < rho)
    (Rprobe Rsecondary : ℕ) (Kcut : ℝ) (hKcut : 0 ≤ Kcut)
    (Tinv Tobs : ℕ → ℝ) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) : Prop :=
    let Csrc := jointGroupedPrescribedZeroSourceCost Pieces m N d d 444 442 (Tp 0) weight
      (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)
    let amplitude := passiveOriginalReserveAmplitude Csrc rho
    let u := passiveOriginalSmallParameter B amplitude
      (passiveOriginalReserveAmplitude_pos Csrc rho hrho) b p₀
    ∃ Ku : ℕ → ℝ, (∀ j, 0 ≤ Ku j) ∧ Ku 0 = amplitude ∧
    let ProbeB := fun j => ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j)*
      jointGroupedPrescribedMeanUniformCost Pieces m N d (j+444) 442 j (Tp j) weight
        (Mgp j) (Bchi j) (Bnu j) (Mphase j) (Ku j)
    ∀ (HBound : ℕ → ℝ) (Rsub Lprimary : ℕ) (reserve : ℝ) (hc : 0 < reserve)
      (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
      (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
      (Tb : ℕ → ℝ) (hTb : ∀ k, 0 ≤ Tb k)
      (hLcard : Fintype.card (Λ ⊕ Fin r) ≤ Lprimary),
    let C := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      440 Rsub Lprimary (by omega) reserve hc Bnd Mg hBnd hMg Tb hTb
    let cap := round4ParameterProbeForcedCap HBound rho ProbeB C 440 444
    let R := round4ParameterProbeForcedProfile HBound ProbeB C 444
    let C0 := fun s => ProbeB s+max 0 (C s (HBound (s+444)))
    let Cd := fun i s => max 0 ((C s (max (R i (s+444)) (R (i+1) (s+444))))*Dinput s)
    ∀ (FirstBnd FirstMg FirstChi FirstNu FirstKu FirstPhase : ℝ)
      (hFirstBnd : 0 ≤ FirstBnd) (hFirstMg : 0 ≤ FirstMg)
      (hFirstChi : 0 ≤ FirstChi) (hFirstNu : 0 ≤ FirstNu)
      (hFirstKu : 0 ≤ FirstKu) (hFirstPhase : 0 ≤ FirstPhase)
      (FirstTb FirstTp : ℕ → ℝ)
      (hFirstTb : ∀ k, 0 ≤ FirstTb k) (hFirstTp : ∀ k, 0 ≤ FirstTp k),
    ∃ CU CE : ℝ, 0 ≤ CU ∧ 0 ≤ CE ∧ 0 < cap ∧
    ∀ (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H : parameterRound2_originalTensorGermSpace A B.chart S univ),
    (∀ s, parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO ell s H ≤ HBound s) →
    ∀ (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k)) (primary : Λ → Set (P × M)),
    Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B.chart S univ
      (parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO ell) H rho
      440 Rsub Lprimary reserve Bnd Mg Dinput Tb F hF g primary ell →
    ∀ (label : (Fin r × Bool) ↪ Fin d)
      (c : (l : Fin r) → Pieces l → P → D → M) (chi : (l : Fin r) → Pieces l → P × D → ℝ)
      (nu : (l : Fin r) → (s : Pieces l) → (p : P) → (x : D) → normalSpace (I := 𝓙) (F p) (c l s p x))
      (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
      (ha : ∀ l s, Round3ParameterChartPreserves (a l s)) (phase : Fin r → P × M → ℝ)
      (Omega : ℕ → Fin A.count × Fin B.count → Set X)
      (hOmega : ∀ j idx, IsOpen (Omega j idx))
      (hOmegaSub : ∀ j idx, Omega j idx ⊆ (B.chart idx.2).target ×ˢ (A.chart idx.1).target)
      (hSamples : ∀ j idx, (parameterTensorModelEquiv (m+1) d) ⁻¹' S idx ⊆ Omega j idx)
      (profiles : ∀ j idx, JointGroupedPrescribedParameterChartRawData F hF c chi nu phase a
        (B.chart idx.2) (A.chart idx.1) (Omega j idx)
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S idx)
        (j+444) j ell (Mgp j) (Bchi j) (Bnu j) (Mphase j) (Tp j))
      (epsilon : ℝ), 0 < epsilon → epsilon < cap → ∀ (delta : ℝ), 0 < delta →
    let vf := fun l s p x => (-(delta*(epsilon*ell))/(weight l)^2) • (chi l s (p,x) • nu l s p x)
    let meanProbe := fun p x => jointGroupedParameterPrescribedMean label F hF c vf phase
      (epsilon*ell) 442 a (u p) p x
    let background := fun i => actualParameterBackgroundMeanIterate F hF g 442
      (epsilon*ell) delta H.val (fun (_ : Fin 0 → ℝ) => meanProbe) i 0
    ∀ (hdeltatau : delta ≤ epsilon*ell)
      (support : (Λ ⊕ Fin r) → Set (P × M))
      (pieceK : (l : Fin r) → Pieces l → Set (P × M))
      (choice : ActualSecondarySignedRecord (Λ ⊕ Fin r) → Sub → Round3ParameterSecondaryChoice P M m)
      (hchoice : ∀ rec s, Round3ParameterChartPreserves (choice rec s).chart)
      (raw : ActualProbeInitialCarrierRawAtlas (Tr := ℝ) A B.chart S F hF g c chi nu phase a
        (background 441) (background 441) u univ primary support pieceK choice 1329 885 440 442 440 Rsub Lprimary Rprobe Rsecondary
        reserve FirstBnd FirstMg Kcut FirstChi FirstNu FirstKu FirstPhase
        (epsilon*ell) ell delta 0 FirstTb FirstTp Tinv Tobs),
    let U := actualProbeInitialGroupedIncrement F hF g label c vf phase (epsilon*ell) delta
      442 442 442 a (background 441) u choice hchoice
    let coordinates := incrementsOriginalMapCoordinates A B.chart U
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B.chart i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 2 440 (epsilon*ell) coordinates (incrementsOriginalDifferentiation A B.chart) S ≠ ⊤ ∧
      (paperAtlasWeighted 2 440 (epsilon*ell) coordinates (incrementsOriginalDifferentiation A B.chart) S).toReal ≤
        CU*delta/(epsilon*ell)) ∧
    (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B.chart) S ≠ ⊤ ∧
      (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B.chart) S).toReal ≤ CU*delta/(epsilon*ell)) ∧
    ∃ error : parameterRound2_originalTensorGermSpace A B.chart S univ,
      error.val = incrementsOriginalMetricError (fun z => F z.1 z.2) U H.val delta ∧
      parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO (epsilon*ell) 440 error ≤
        CE*(delta*((epsilon*ell)/ell)^440+delta^3/(epsilon*ell))

set_option backward.isDefEq.respectTransparency true in
theorem actualProbeInitialSupply_carrier_q440_complete_from_raw
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (S : Fin A.count × Fin B.count → Set (Fin (m+1+d) → ℝ))
    (hS : ∀ idx, IsCompact (S idx))
    (hSO : ∀ idx, S idx ⊆ incrementsOriginalDifferentiation A B.chart idx)
    (hSQ : ∀ idx z, parameterTensorModelEquiv (m+1) d z ∈ S idx → z.1 ∈ Q idx.2)
    (Tp : ℕ → ℕ → ℝ) (hTp : ∀ j k, 0 ≤ Tp j k)
    (weight : Fin r → ℝ) (hweight : ∀ l, weight l ≠ 0) (Mgp Bchi Bnu Mphase : ℕ → ℝ)
    (hMgp : ∀ j, 0 ≤ Mgp j) (hBchi : ∀ j, 0 ≤ Bchi j)
    (hBnu : ∀ j, 0 ≤ Bnu j) (hMphase : ∀ j, 0 ≤ Mphase j)
    (rho : ℝ) (hrho : 0 < rho)
    (Rprobe Rsecondary : ℕ) (Kcut : ℝ) (hKcut : 0 ≤ Kcut)
    (Tinv Tobs : ℕ → ℝ) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    actualProbeInitialCarrierQ440RawStatement (m := m) (d := d) (N := N) (Tr := Tr) (Λ := Λ) (Β := Β) (Pieces := Pieces) (Sub := Sub)
      A hA B hB Q hQ hQT b p₀ hp₀ S hS hSO hSQ Tp hTp weight hweight
      Mgp Bchi Bnu Mphase hMgp hBchi hBnu hMphase rho hrho
      Rprobe Rsecondary Kcut hKcut Tinv Tobs hTinv hTobs := by
  unfold actualProbeInitialCarrierQ440RawStatement
  intro Csrc amplitude u
  obtain ⟨Ku,hKu,hKu0,hproduce⟩ := jointBackground_grouped_q440_physical_mean_producer
    (m := m) (d := d) (N := N) (Tr := Tr) (Λ := Λ) (Β := Β) (Sub := Pieces)
    A hA B hB Q hQ hQT b p₀ hp₀ S hS hSO hSQ Tp hTp weight Mgp Bchi Bnu Mphase
    hMgp hBchi hBnu hMphase rho hrho
  refine ⟨Ku,hKu,hKu0,?_⟩
  intro ProbeB HBound Rsub Lprimary reserve hc Bnd Mg Dinput hBnd hMg hDinput Tb hTb hLcard C cap R C0 Cd
    FirstBnd FirstMg FirstChi FirstNu FirstKu FirstPhase hFirstBnd hFirstMg
    hFirstChi hFirstNu hFirstKu hFirstPhase FirstTb FirstTp hFirstTb hFirstTp
  obtain ⟨CU,hCU,hMap⟩ := actualProbeInitialSupply_carrier_original_map_from_raw
    (M := M) (P := P) (Tr := ℝ) (m := m) (d := d) (N := N) (p := d) (count := B.count)
    (Λ := Λ) (Β := Β) (Pieces := Pieces) (Sub := Sub)
    1329 885 440 442 440 442 Rsub Lprimary Rprobe Rsecondary (by omega) (by omega) (by omega) (by omega)
    hLcard reserve FirstBnd FirstMg Kcut FirstChi FirstNu FirstKu FirstPhase
    hc hFirstBnd hFirstMg hKcut hFirstChi hFirstNu hFirstKu hFirstPhase
    weight FirstTb FirstTp Tinv Tobs hFirstTb hFirstTp hTinv hTobs
  obtain ⟨CR,hCR,hRest⟩ := actualProbeInitialSupply_carrier_original_remainder_from_raw
    (M := M) (P := P) (Tr := ℝ) (m := m) (d := d) (N := N) (p := d) (count := B.count)
    (Λ := Λ) (Β := Β) (Pieces := Pieces) (Sub := Sub)
    1329 885 440 442 440 442 Rsub Lprimary Rprobe Rsecondary (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hLcard
    reserve FirstBnd FirstMg Kcut FirstChi FirstNu FirstKu FirstPhase
    hc hFirstBnd hFirstMg hKcut hFirstChi hFirstNu hFirstKu hFirstPhase
    weight hweight FirstTb FirstTp Tinv Tobs hFirstTb hFirstTp hTinv hTobs
  let CM := max (parameterRound2_finiteMeanErrorCost C0 Cd 444 441 440) 0
  have hCM : 0 ≤ CM := le_max_right _ _
  refine ⟨CU,CR+CM,hCU,add_nonneg hCR hCM,?_,?_⟩
  · exact round4ParameterProbeForcedCap_pos HBound rho hrho ProbeB C 440 444
  intro ell hell hell1 H hH F hF g hg primary supply label c chi nu a ha phase
    Omega hOmega hOmegaSub hSamples profiles epsilon he hecap delta hdelta
    vf meanProbe background hdeltatau support pieceK choice hchoice raw U coordinates
  obtain ⟨K,hvalue,hreserve,hbound,hraw,Mean,hMean,hMeanBound⟩ :=
    (hproduce H HBound Rsub Lprimary reserve hc Bnd Mg Dinput hBnd hMg hDinput Tb hTb).2
      ell hell hell1 hH F hF g hg primary supply label c chi nu a ha phase Omega hOmega
      hOmegaSub hSamples profiles epsilon he hecap delta hdelta
  have he1 : epsilon ≤ 1 := (hecap.trans_le (min_le_left _ _)).le
  have htau : 0 < epsilon*ell := mul_pos he hell
  have htaul : epsilon*ell ≤ ell := by nlinarith
  have hmap := hMap A B.chart S F hF g hg label c chi nu phase a ha
    (background 441) (background 441) u univ primary support pieceK choice hchoice (epsilon*ell) ell delta 0
    htau htaul hell1 hdelta.le hdeltatau raw
  obtain ⟨Rest,hRestValue,hRestBound⟩ := hRest A hA B.chart S hS hSO F hF g hg label c chi nu phase a ha
    (background 441) (background 441) u univ primary support pieceK choice hchoice (epsilon*ell) ell delta 0
    htau htaul hell1 hdelta.le hdeltatau raw
  have hMeanCost : parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO ell 440 Mean ≤
      delta^2*((epsilon*ell/ell)^(440+1)*CM) := by
    have hm := hMeanBound 440
    change _ ≤ _ at hm
    rw [mul_div_cancel_right₀ _ hell.ne']
    exact hm.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg he.le _)) (sq_nonneg delta))
  have herr := actualProbeInitialSupply_same_mean_germ_add A B.chart S univ hS hSO
    (fun z => F z.1 z.2) U
    (actualProbeInitialGroupedMean F hF g label c vf phase (epsilon*ell) delta
      442 442 a (background 441) u)
    H.val 440 440 delta (epsilon*ell) ell CR CM hdelta.le hdeltatau htau htaul hell1 hCM
    Rest Mean hRestValue hMean hRestBound hMeanCost
  exact ⟨hmap.1,hmap.2.1,hmap.2.2,herr⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_carrier_q440_complete_from_raw
