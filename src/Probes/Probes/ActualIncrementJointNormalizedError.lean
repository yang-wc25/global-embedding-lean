import Probes.ActualIncrementJointCorrectionDifference
import Probes.ActualIncrementJointCorrectionSum
import GlobalEmbedding.Paper.IncrementsActualNormalizedPrimaryError

/-! The SAME original normalized primary error now has full parameter/source
jet and SAME-input difference bounds. Actual reconstruction is always the
original per-parameter spatial finite polynomial. Only primitive input,
source and geometry profiles occur; no correction/error estimate is assumed.
The finite loss is p+2 and the subordinate cap is fixed before its index type. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m+1) → ℂ

theorem actual_joint_normalized_primary_error_bounds_uniform
    (j p : ℕ) (v : D) (coord : Fin N) (c Bnd K : ℝ) (Bsub : ℕ)
    (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {A : Type*} [Fintype A] (_hCard : Fintype.card A ≤ Bsub)
        (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b)) (chart : Ep → D → M),
      ∀ {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
        (O S : Set X) (_hO : IsOpen O) (_hSO : S ⊆ O)
        (L : X → T →L[ℝ] ℝ) (input inputbar : X → T)
        (cutoff phi : X → ℝ) (normal : X → V)
        (_hL : ContDiffOn ℝ ∞ L O) (_hInput : ContDiffOn ℝ ∞ input O)
        (_hInputbar : ContDiffOn ℝ ∞ inputbar O) (_hCut : ContDiffOn ℝ ∞ cutoff O)
        (_hPhi : ContDiffOn ℝ ∞ phi O) (_hNormal : ContDiffOn ℝ ∞ normal O)
        (_hA : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (chart z.1) z.2) O)
        (_hB : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (chart z.1) z.2) O)
        (_hG : ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ chart z.1) z.2)) O)
        (_hJ : ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (chart z.1 z.2)).subtypeL.comp
          (incrementsModeCoordinateJ (F z.1) (hF z.1) (chart z.1) z.2)) O)
        (_hT0 : ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (chart z.1) z.2) O)
        (k kbar : A → X → Cdata) (_hk : ∀ a, ContDiffOn ℝ ∞ (k a) O)
        (_hkbar : ∀ a, ContDiffOn ℝ ∞ (kbar a) O)
        (ell tau Delta : ℝ) (_hell : 0 < ell) (_hell1 : ell ≤ 1)
        (_htau : 0 < tau) (_htauell : tau ≤ ell) (_hDelta : 0 ≤ Delta)
        (_hReserve : ∀ x ∈ S, c ≤ L x (input x) ∧ c ≤ L x (inputbar x))
        (_hLb : ∀ i ≤ j + p + 2, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ Bnd)
        (_hInputb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i input x‖ ≤ Bnd)
        (_hInputbarb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i inputbar x‖ ≤ Bnd)
        (_hCutb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i cutoff x‖ ≤ Bnd)
        (_hNormalb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i normal x‖ ≤ Bnd)
        (_hInputd : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ input y - inputbar y) x‖ ≤ Delta)
        (_hAb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (chart z.1) z.2) x‖ ≤ Bnd)
        (_hBb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (chart z.1) z.2) x‖ ≤ Bnd)
        (_hGb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ chart z.1) z.2)) x‖ ≤ Bnd)
        (_hJb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun z : X => (normalSpace (I := I) (F z.1) (chart z.1 z.2)).subtypeL.comp
            (incrementsModeCoordinateJ (F z.1) (hF z.1) (chart z.1) z.2)) x‖ ≤ Bnd)
        (_hT0b : ∀ i ≤ j + 1, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z : X => incrementsModeTransverseValue (F z.1) (chart z.1) z.2) x‖ ≤ Bnd)
        (_hkb : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (k a) x‖ ≤ K * tau)
        (_hkbarb : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (kbar a) x‖ ≤ K * tau)
        (_hkd : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ k a y - kbar a y) x‖ ≤ K * tau * Delta)
        (_hPhib : ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z : X => fderiv ℝ (fun x => phi (z.1,x)) z.2 v) x‖ ≤ Bnd),
      let err := fun z : X => incrementsActualNormalizedPrimaryError (F z.1) (hF z.1)
        (chart z.1) (fun x => L (z.1,x)) (fun x => input (z.1,x))
        (fun x => cutoff (z.1,x)) (fun x => phi (z.1,x)) (fun x => normal (z.1,x))
        (fun a x => k a (z.1,x)) tau p v coord z.2
      let errbar := fun z : X => incrementsActualNormalizedPrimaryError (F z.1) (hF z.1)
        (chart z.1) (fun x => L (z.1,x)) (fun x => inputbar (z.1,x))
        (fun x => cutoff (z.1,x)) (fun x => phi (z.1,x)) (fun x => normal (z.1,x))
        (fun a x => kbar a (z.1,x)) tau p v coord z.2
      let positive := O ∩ {z | 0 < L z (input z)} ∩ {z | 0 < L z (inputbar z)}
      (ContDiffOn ℝ ∞ err positive ∧ ContDiffOn ℝ ∞ errbar positive) ∧
      (∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i err x‖ ≤ C * (tau / ell)) ∧
      (∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i errbar x‖ ≤ C * (tau / ell)) ∧
      (∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
        (fun y ↦ err y - errbar y) x‖ ≤ C * (tau / ell) * Delta) := by
  obtain ⟨Cs,hCs,hsize⟩ := increments_positive_reserve_amplitude_scaled_jets (j+1) c Bnd hc hBnd
  obtain ⟨Cd,hCd,hdifference⟩ :=
    increments_positive_reserve_amplitude_difference_scaled_jets (j+1) c Bnd hc hBnd
  let Cv := max Cs Cd * Real.sqrt 2
  let Cr := actualJointHomogeneousReconstructionCost m (j+1) Bnd
  let profile : ℝ := ∑ a ∈ Finset.range p, (2*2^(j+p+2)*Bnd)^a
  let TP := Cr * ‖incrementsModeRealPart (m := m)‖ * K * profile
  let TQ := Cr * ‖incrementsModeImagPart (m := m)‖ * K * profile
  let Cz := actualJointCorrectionSumCost N Bsub coord TP TQ
  have hCv : 0 ≤ Cv := by unfold Cv; positivity
  have hCr : 0 ≤ Cr := actualJointHomogeneousReconstructionCost_nonneg m (j+1) hBnd
  have hprof : 0 ≤ profile := by unfold profile; positivity
  have hTP : 0 ≤ TP := by unfold TP; positivity
  have hTQ : 0 ≤ TQ := by unfold TQ; positivity
  have hCz : 0 ≤ Cz := actualJointCorrectionSumCost_nonneg Bsub coord hTP hTQ
  refine ⟨actualJointPrimaryErrorCost j v coord Cv Cz Bnd,
    actualJointPrimaryErrorCost_nonneg j v coord hCv hCz hBnd,?_⟩
  intro A _ hCard F hF chart T _ _ O S hO hSO L input inputbar cutoff phi normal
    hL hInput hInputbar hCut hPhi hNormal hA hB hG hJ hT0 k kbar hk hkbar
    ell tau Delta hell hell1 htau htauell hDelta hReserve hLb hInputb hInputbarb hCutb
    hNormalb hInputd hAb hBb hGb hJb hT0b hkb hkbarb hkd hPhib err errbar positive
  let b := fun z : X => cutoff z * Real.sqrt (L z (input z))
  let bbar := fun z : X => cutoff z * Real.sqrt (L z (inputbar z))
  have hPos : IsOpen positive := by
    have ha : IsOpen (O ∩ {z | 0 < L z (input z)}) :=
      (hL.clm_apply hInput).continuousOn.isOpen_inter_preimage hO isOpen_Ioi
    have hb : IsOpen (O ∩ {z | 0 < L z (inputbar z)}) :=
      (hL.clm_apply hInputbar).continuousOn.isOpen_inter_preimage hO isOpen_Ioi
    convert ha.inter hb using 1
    ext z
    simp only [positive,Set.mem_inter_iff,Set.mem_setOf_eq]
    tauto
  have hPosO : positive ⊆ O := fun z hz => hz.1.1
  have hSpos : S ⊆ positive := fun z hz =>
    ⟨⟨hSO hz,hc.trans_le (hReserve z hz).1⟩,hc.trans_le (hReserve z hz).2⟩
  have hb : ContDiffOn ℝ ∞ b positive :=
    (hCut.mono hPosO).mul (((hL.clm_apply hInput).mono hPosO).sqrt (fun z hz => hz.1.2.ne'))
  have hbbar : ContDiffOn ℝ ∞ bbar positive :=
    (hCut.mono hPosO).mul (((hL.clm_apply hInputbar).mono hPosO).sqrt (fun z hz => hz.2.ne'))
  let wA := fun z : X => b z • normal z
  let wB := fun z : X => bbar z • normal z
  have hwA : ContDiffOn ℝ ∞ wA positive := hb.smul (hNormal.mono hPosO)
  have hwB : ContDiffOn ℝ ∞ wB positive := hbbar.smul (hNormal.mono hPosO)
  have hwAb := hsize O S hO hSO L input cutoff normal hL hInput hCut hNormal ell hell
    (fun z hz => (hReserve z hz).1)
    (fun r hr z hz => hLb r (by omega) z hz)
    (fun r hr z hz => hInputb r (by omega) z hz)
    (fun r hr z hz => hCutb r (by omega) z hz)
    (fun r hr z hz => hNormalb r (by omega) z hz)
  have hwBb := hsize O S hO hSO L inputbar cutoff normal hL hInputbar hCut hNormal ell hell
    (fun z hz => (hReserve z hz).2)
    (fun r hr z hz => hLb r (by omega) z hz)
    (fun r hr z hz => hInputbarb r (by omega) z hz)
    (fun r hr z hz => hCutb r (by omega) z hz)
    (fun r hr z hz => hNormalb r (by omega) z hz)
  have hwDb := hdifference O S hO hSO L input inputbar cutoff normal hL hInput hInputbar
    hCut hNormal ell Delta hell hDelta hReserve
    (fun r hr z hz => hLb r (by omega) z hz)
    (fun r hr z hz => hInputb r (by omega) z hz)
    (fun r hr z hz => hInputbarb r (by omega) z hz)
    (fun r hr z hz => hCutb r (by omega) z hz)
    (fun r hr z hz => hNormalb r (by omega) z hz)
    (fun r hr z hz => hInputd r (by omega) z hz)
  let s := Real.sqrt 2 * 1 * tau
  have hs : |s| = Real.sqrt 2 * tau := by
    dsimp [s]
    rw [mul_one,abs_mul,abs_of_nonneg (Real.sqrt_nonneg 2),abs_of_pos htau]
  have hscale (w : X → V) (hw : ContDiffOn ℝ ∞ w positive) (B : ℝ)
      (hwb : ∀ r ≤ j+1, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r w z‖ ≤ B) :
      ∀ r ≤ j+1, ∀ z ∈ S,
        ell^r*‖iteratedFDeriv ℝ r (fun y => s • w y) z‖ ≤ B*Real.sqrt 2*tau := by
    intro r hr z hz
    rw [iteratedFDeriv_const_smul_apply' ((hw.contDiffAt (hPos.mem_nhds (hSpos hz))).of_le
      (by simp : (r : ℕ∞ω) ≤ ∞)),norm_smul,Real.norm_eq_abs]
    calc
      _ = |s| * (ell^r*‖iteratedFDeriv ℝ r w z‖) := by ring
      _ ≤ |s| * B := mul_le_mul_of_nonneg_left (hwb r hr z hz) (abs_nonneg s)
      _ = _ := by rw [hs]; ring
  let VF := fun (b : X → ℝ) (z : X) => (Real.sqrt 2*1*tau*b z) • normal z
  have hVAb : ∀ r ≤ j+1, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r (VF b) z‖ ≤ Cv*tau := by
    intro r hr z hz
    have hh := hscale wA hwA Cs hwAb r hr z hz
    change ell^r*‖iteratedFDeriv ℝ r (fun y => s • (b y • normal y)) z‖ ≤ _ at hh
    simp only [smul_smul] at hh
    apply hh.trans
    dsimp only [Cv]
    gcongr
    exact le_max_left _ _
  have hVBb : ∀ r ≤ j+1, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r (VF bbar) z‖ ≤ Cv*tau := by
    intro r hr z hz
    have hh := hscale wB hwB Cs hwBb r hr z hz
    change ell^r*‖iteratedFDeriv ℝ r (fun y => s • (bbar y • normal y)) z‖ ≤ _ at hh
    simp only [smul_smul] at hh
    apply hh.trans
    dsimp only [Cv]
    gcongr
    exact le_max_left _ _
  have hVD : ∀ r ≤ j+1, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r
      (fun y => VF b y-VF bbar y) z‖ ≤ Cv*tau*Delta := by
    intro r hr z hz
    have hh := hscale (fun y => wA y-wB y) (hwA.sub hwB) (Cd*Delta) hwDb r hr z hz
    have heq : (fun y => s • (wA y-wB y)) = (fun y => VF b y-VF bbar y) := by
      funext y
      simp only [wA,wB,VF,smul_sub,smul_smul,s]
    rw [heq] at hh
    apply hh.trans
    calc
      _ = (Cd*Real.sqrt 2)*tau*Delta := by ring
      _ ≤ _ := by dsimp only [Cv]; gcongr; exact le_max_right _ _
  let R := fun (ch : Cdata →L[ℝ] D) (source : X → Cdata) (z : X) =>
    incrementsPrimaryReconstructedChannel (F z.1) (hF z.1) (chart z.1) ch tau p
      (fun x => source (z.1,x)) z.2
  have hCor (ch : Cdata →L[ℝ] D) (source : X → Cdata)
      (hsource : ContDiffOn ℝ ∞ source O)
      (hsb : ∀ r ≤ j+p+2, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r source z‖ ≤ K*tau) :
      ContDiffOn ℝ ∞ (R ch source) O ∧ ∀ r ≤ j+1, ∀ z ∈ S,
        ell^(r+1)*‖iteratedFDeriv ℝ r (R ch source) z‖ ≤
          (Cr*‖ch‖*K*profile)*tau^2 := by
    obtain ⟨_,hr,hrb⟩ := actual_joint_finite_channel_reconstruction F hF chart source ch
      (j+p+2) p (j+1) (by omega) O S hO hSO hA hB hG hJ hT0 hsource
      tau ell Bnd (K*tau) htau htauell hell1 hBnd (mul_nonneg hK htau.le)
      hAb hBb hGb hJb hT0b hsb
    refine ⟨hr,?_⟩
    intro r hr z hz
    exact (hrb r hr z hz).trans_eq (by dsimp only [Cr,profile]; ring)
  have hCord (ch : Cdata →L[ℝ] D) (a : A) :
      ∀ r ≤ j+1, ∀ z ∈ S, ell^(r+1)*‖iteratedFDeriv ℝ r
        (fun y => R ch (k a) y-R ch (kbar a) y) z‖ ≤
          (Cr*‖ch‖*K*profile)*tau^2*Delta := by
    obtain ⟨_,hrb⟩ := actual_joint_reconstructed_channel_difference_jets F hF chart (k a)
      (kbar a) ch (j+p+2) p (j+1) (by omega) O S hO hSO hA hB hG hJ hT0 (hk a) (hkbar a)
      tau ell Bnd (K*tau*Delta) htau htauell hell1 hBnd (by positivity)
      hAb hBb hGb hJb hT0b (hkd a)
    intro r hr z hz
    exact (hrb r hr z hz).trans_eq (by dsimp only [Cr,profile]; ring)
  let P := fun a => R incrementsModeRealPart (k a)
  let Q := fun a => R incrementsModeImagPart (k a)
  let Pbar := fun a => R incrementsModeRealPart (kbar a)
  let Qbar := fun a => R incrementsModeImagPart (kbar a)
  have hPs : ∀ a, ContDiffOn ℝ ∞ (P a) O := fun a => (hCor _ _ (hk a) (hkb a)).1
  have hQs : ∀ a, ContDiffOn ℝ ∞ (Q a) O := fun a => (hCor _ _ (hk a) (hkb a)).1
  have hPbs : ∀ a, ContDiffOn ℝ ∞ (Pbar a) O := fun a => (hCor _ _ (hkbar a) (hkbarb a)).1
  have hQbs : ∀ a, ContDiffOn ℝ ∞ (Qbar a) O := fun a => (hCor _ _ (hkbar a) (hkbarb a)).1
  let Csum := fun (P Q : A → X → V) (z : X) => ∑ a,
    (incrementsFreeComplexCoordinate coord (P a z)+Complex.I • incrementsFreeComplexCoordinate coord (Q a z))
  obtain ⟨_,hCA⟩ := actual_joint_correction_sum_slow_jets (j+1) Bsub coord hCard P Q O S hO hSO
    hPs hQs ell tau TP TQ hell.le hTP hTQ
    (fun a => (hCor _ _ (hk a) (hkb a)).2) (fun a => (hCor _ _ (hk a) (hkb a)).2)
  obtain ⟨_,hCB⟩ := actual_joint_correction_sum_slow_jets (j+1) Bsub coord hCard Pbar Qbar O S hO hSO
    hPbs hQbs ell tau TP TQ hell.le hTP hTQ
    (fun a => (hCor _ _ (hkbar a) (hkbarb a)).2) (fun a => (hCor _ _ (hkbar a) (hkbarb a)).2)
  obtain ⟨_,hCDraw⟩ := actual_joint_correction_sum_slow_jets (j+1) Bsub coord hCard
    (fun a y => P a y-Pbar a y) (fun a y => Q a y-Qbar a y) O S hO hSO
    (fun a => (hPs a).sub (hPbs a)) (fun a => (hQs a).sub (hQbs a)) ell tau
    (TP*Delta) (TQ*Delta) hell.le (by positivity) (by positivity)
    (fun a r hr z hz => (hCord _ a r hr z hz).trans_eq (by dsimp only [TP]; ring))
    (fun a r hr z hz => (hCord _ a r hr z hz).trans_eq (by dsimp only [TQ]; ring))
  have hCDeq : Csum (fun a y => P a y-Pbar a y) (fun a y => Q a y-Qbar a y) =
      (fun y => Csum P Q y-Csum Pbar Qbar y) := by
    funext y
    dsimp only [Csum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [map_sub,smul_sub]
    abel
  have hCD : ∀ r ≤ j+1, ∀ z ∈ S, ell^(r+1)*‖iteratedFDeriv ℝ r
      (fun y => Csum P Q y-Csum Pbar Qbar y) z‖ ≤ Cz*tau^2*Delta := by
    rw [← hCDeq]
    intro r hr z hz
    exact (hCDraw r hr z hz).trans_eq (by dsimp only [Cz,actualJointCorrectionSumCost]; ring)
  obtain ⟨hsA,hbA⟩ := actual_joint_primary_error_slow_jets b phi normal P Q v coord positive S
    hPos hSpos hb (hNormal.mono hPosO) (hPhi.mono hPosO)
    (fun a => (hPs a).mono hPosO) (fun a => (hQs a).mono hPosO)
    j ell tau Cv Cz Bnd hell htau htauell hCv hCz hBnd hVAb hCA hPhib
  obtain ⟨hsB,hbB⟩ := actual_joint_primary_error_slow_jets bbar phi normal Pbar Qbar v coord positive S
    hPos hSpos hbbar (hNormal.mono hPosO) (hPhi.mono hPosO)
    (fun a => (hPbs a).mono hPosO) (fun a => (hQbs a).mono hPosO)
    j ell tau Cv Cz Bnd hell htau htauell hCv hCz hBnd hVBb hCB hPhib
  obtain ⟨_,hbD⟩ := actual_joint_primary_error_difference_slow_jets b bbar phi normal
    P Q Pbar Qbar v coord positive S hPos hSpos hb hbbar (hNormal.mono hPosO) (hPhi.mono hPosO)
    (fun a => (hPs a).mono hPosO) (fun a => (hQs a).mono hPosO)
    (fun a => (hPbs a).mono hPosO) (fun a => (hQbs a).mono hPosO)
    j ell tau Cv Cz Bnd Delta hell htau htauell hCv hCz hBnd hDelta hVD hCD hPhib
  exact ⟨⟨hsA,hsB⟩,hbA,hbB,hbD⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_normalized_primary_error_bounds_uniform
