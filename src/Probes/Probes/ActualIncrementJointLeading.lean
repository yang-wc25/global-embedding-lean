import Probes.ActualIncrementJointPrimaryError
import GlobalEmbedding.Paper.IncrementsNormalizedPrimaryFreeCoefficients

/-! The literal leading coefficient of the SAME normalized primary wave,
with all parameter/source derivatives and its same-input tame difference.
The constant is chosen before every input field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem actual_joint_normalized_primary_leading_bounds_uniform
    (coord : Fin N) (v : D) (j : ℕ) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
        (O S : Set X) (_hO : IsOpen O) (_hSO : S ⊆ O)
        (L : X → T →L[ℝ] ℝ) (input inputbar : X → T)
        (cutoff phi : X → ℝ) (normal : X → V)
        (_hL : ContDiffOn ℝ ∞ L O) (_hInput : ContDiffOn ℝ ∞ input O)
        (_hInputbar : ContDiffOn ℝ ∞ inputbar O) (_hCut : ContDiffOn ℝ ∞ cutoff O)
        (_hPhi : ContDiffOn ℝ ∞ phi O) (_hNormal : ContDiffOn ℝ ∞ normal O)
        (ell Delta : ℝ) (_hell : 0 < ell) (_hDelta : 0 ≤ Delta)
        (_hReserve : ∀ z ∈ S, c ≤ L z (input z) ∧ c ≤ L z (inputbar z))
        (_hLb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r L z‖ ≤ M)
        (_hInputb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r input z‖ ≤ M)
        (_hInputbarb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r inputbar z‖ ≤ M)
        (_hCutb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r cutoff z‖ ≤ M)
        (_hNormalb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r normal z‖ ≤ M)
        (_hPhib : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
          (fun y : X => fderiv ℝ (fun x => phi (y.1,x)) y.2 v) z‖ ≤ M)
        (_hInputd : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
          (fun y => input y-inputbar y) z‖ ≤ Delta),
      let leadA := fun z : X => incrementsLeadingCoefficient 1
        (cutoff z * Real.sqrt (L z (input z))) (normal z)
        (fun _ : Unit => fderiv ℝ (fun x => phi (z.1,x)) z.2 v) () coord
      let leadB := fun z : X => incrementsLeadingCoefficient 1
        (cutoff z * Real.sqrt (L z (inputbar z))) (normal z)
        (fun _ : Unit => fderiv ℝ (fun x => phi (z.1,x)) z.2 v) () coord
      let positive := O ∩ {z | 0 < L z (input z)} ∩ {z | 0 < L z (inputbar z)}
      (ContDiffOn ℝ ∞ leadA positive ∧ ContDiffOn ℝ ∞ leadB positive) ∧
      (∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r leadA z‖ ≤ C) ∧
      (∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r leadB z‖ ≤ C) ∧
      (∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun y => leadA y-leadB y) z‖ ≤ C*Delta) := by
  obtain ⟨Cs,hCs,hsize⟩ := increments_positive_reserve_amplitude_scaled_jets j c M hc hM
  obtain ⟨Cd,hCd,hdifference⟩ :=
    increments_positive_reserve_amplitude_difference_scaled_jets j c M hc hM
  let H : ℝ →L[ℝ] V →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight
    (Real.sqrt 2 • (Complex.I • incrementsFreeComplexCoordinate coord))
  let Cv := max Cs Cd
  have hCv : 0 ≤ Cv := hCs.trans (le_max_left _ _)
  refine ⟨2^j * (‖H‖*M)*Cv,by positivity,?_⟩
  intro T _ _ O S hO hSO L input inputbar cutoff phi normal hL hInput hInputbar
    hCut hPhi hNormal ell Delta hell hDelta hReserve hLb hInputb hInputbarb hCutb
    hNormalb hPhib hInputd leadA leadB positive
  have hPos : IsOpen positive := by
    have ha : IsOpen (O ∩ {z | 0 < L z (input z)}) :=
      (hL.clm_apply hInput).continuousOn.isOpen_inter_preimage hO isOpen_Ioi
    have hb : IsOpen (O ∩ {z | 0 < L z (inputbar z)}) :=
      (hL.clm_apply hInputbar).continuousOn.isOpen_inter_preimage hO isOpen_Ioi
    convert ha.inter hb using 1
    ext z
    simp only [positive,Set.mem_inter_iff,Set.mem_ofPred_eq]
    tauto
  have hPosO : positive ⊆ O := fun z hz => hz.1.1
  have hSpos : S ⊆ positive := fun z hz =>
    ⟨⟨hSO hz,hc.trans_le (hReserve z hz).1⟩,hc.trans_le (hReserve z hz).2⟩
  let wA := fun z : X => (cutoff z*Real.sqrt (L z (input z))) • normal z
  let wB := fun z : X => (cutoff z*Real.sqrt (L z (inputbar z))) • normal z
  have hwA : ContDiffOn ℝ ∞ wA positive :=
    ((hCut.mono hPosO).mul (((hL.clm_apply hInput).mono hPosO).sqrt
      (fun z hz => hz.1.2.ne'))).smul (hNormal.mono hPosO)
  have hwB : ContDiffOn ℝ ∞ wB positive :=
    ((hCut.mono hPosO).mul (((hL.clm_apply hInputbar).mono hPosO).sqrt
      (fun z hz => hz.2.ne'))).smul (hNormal.mono hPosO)
  let g := fun z : X => fderiv ℝ (fun x => phi (z.1,x)) z.2 v
  have hg : ContDiffOn ℝ ∞ g O :=
    ((incrementsJointSpatialJets_bridge phi O hO hPhi).2.1).clm_apply contDiffOn_const
  have hvalA := hsize O S hO hSO L input cutoff normal hL hInput hCut hNormal ell hell
    (fun z hz => (hReserve z hz).1) hLb hInputb hCutb hNormalb
  have hvalB := hsize O S hO hSO L inputbar cutoff normal hL hInputbar hCut hNormal ell hell
    (fun z hz => (hReserve z hz).2) hLb hInputbarb hCutb hNormalb
  have hvalD := hdifference O S hO hSO L input inputbar cutoff normal hL hInput hInputbar
    hCut hNormal ell Delta hell hDelta hReserve hLb hInputb hInputbarb hCutb hNormalb hInputd
  have hEqA : leadA = fun z => H (g z) (wA z) := by
    funext z
    change Complex.I * (Real.sqrt 2*1*(cutoff z*Real.sqrt (L z (input z)))*
      normal z coord*g z : ℝ) = g z • (Real.sqrt 2 • (Complex.I •
        ((cutoff z*Real.sqrt (L z (input z))*normal z coord : ℝ) : ℂ)))
    simp only [Complex.real_smul,smul_eq_mul]
    push_cast
    ring
  have hEqB : leadB = fun z => H (g z) (wB z) := by
    funext z
    change Complex.I * (Real.sqrt 2*1*(cutoff z*Real.sqrt (L z (inputbar z)))*
      normal z coord*g z : ℝ) = g z • (Real.sqrt 2 • (Complex.I •
        ((cutoff z*Real.sqrt (L z (inputbar z))*normal z coord : ℝ) : ℂ)))
    simp only [Complex.real_smul,smul_eq_mul]
    push_cast
    ring
  have hEqD : (fun z => leadA z-leadB z) = fun z => H (g z) (wA z-wB z) := by
    rw [hEqA,hEqB]
    funext z
    exact (map_sub (H (g z)) _ _).symm
  have hLA : ContDiffOn ℝ ∞ leadA positive := by
    rw [hEqA]
    exact (H.contDiff.comp_contDiffOn (hg.mono hPosO)).clm_apply hwA
  have hLB : ContDiffOn ℝ ∞ leadB positive := by
    rw [hEqB]
    exact (H.contDiff.comp_contDiffOn (hg.mono hPosO)).clm_apply hwB
  refine ⟨⟨hLA,hLB⟩,?_,?_,?_⟩
  · rw [hEqA]
    intro r hr z hz
    have hh := slow_bilinear_jet_bound_norm H positive hPos g wA (hg.mono hPosO) hwA
      r ell M Cs hell.le z (hSpos hz) (fun k hk => hPhib k (hk.trans hr) z hz)
      (fun k hk => hvalA k (hk.trans hr) z hz)
    exact hh.trans (by dsimp only [Cv]; gcongr <;> norm_num)
  · rw [hEqB]
    intro r hr z hz
    have hh := slow_bilinear_jet_bound_norm H positive hPos g wB (hg.mono hPosO) hwB
      r ell M Cs hell.le z (hSpos hz) (fun k hk => hPhib k (hk.trans hr) z hz)
      (fun k hk => hvalB k (hk.trans hr) z hz)
    exact hh.trans (by dsimp only [Cv]; gcongr <;> norm_num)
  · rw [hEqD]
    intro r hr z hz
    have hh := slow_bilinear_jet_bound_norm H positive hPos g (fun z => wA z-wB z)
      (hg.mono hPosO) (hwA.sub hwB) r ell M (Cd*Delta) hell.le z (hSpos hz)
      (fun k hk => hPhib k (hk.trans hr) z hz) (fun k hk => hvalD k (hk.trans hr) z hz)
    calc
      _ ≤ 2^r*(‖H‖*M)*(Cd*Delta) := hh
      _ = (2^r*(‖H‖*M)*Cd)*Delta := by ring
      _ ≤ _ := by dsimp only [Cv]; gcongr <;> norm_num

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_normalized_primary_leading_bounds_uniform
