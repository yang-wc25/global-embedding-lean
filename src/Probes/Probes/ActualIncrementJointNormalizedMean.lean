import Probes.ActualIncrementJointNormalizedError
import Probes.ActualIncrementJointLeading
import GlobalEmbedding.Paper.IncrementsActualNormalizedPrimaryError

/-! The SAME original normalized primary mean has full joint parameter/source
size and tame difference, with p+2 finite derivative loss. Constants precede
subordinate index types, and the real finite-Cj conclusions use the original
paper carrier. The original mean/polarization is never replaced. -/

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

private theorem actual_joint_mean_scaled_pi {X0 ι Y : Type*} [NormedAddCommGroup X0]
    [NormedSpace ℝ X0] [Fintype ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X0 → ι → Y) (x : X0) (hf : ContDiffAt ℝ ∞ f x) (k : ℕ)
    (ell C : ℝ) (hell : 0 < ell) (hC : 0 ≤ C)
    (hb : ∀ a, ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ f y a) x‖ ≤ C) :
    ell ^ k * ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  have he : iteratedFDeriv ℝ k f x = ContinuousMultilinearMap.pi
      (fun a ↦ iteratedFDeriv ℝ k (fun y ↦ f y a) x) := by
    ext w a
    have hp := (ContinuousLinearMap.proj a).iteratedFDeriv_comp_left hf
      (by simp : (k : WithTop ℕ∞) ≤ ∞)
    exact (congrArg (fun t ↦ t w) hp).symm
  rw [he, ContinuousMultilinearMap.opNorm_pi, mul_comm (ell ^ k)]
  apply (le_div_iff₀ (pow_pos hell k)).mp
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hC (pow_nonneg hell.le k))).2
  intro a
  exact (le_div_iff₀ (pow_pos hell k)).2 (by simpa [mul_comm] using hb a)

theorem actual_joint_normalized_mean_bounds_uniform {J : Type*} [Fintype J]
    (j p : ℕ) (v : J → D) (i i' : J) (c Bnd K : ℝ) (Bsub : ℕ)
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
        (_hPhib : ∀ d, ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z : X => fderiv ℝ (fun x => phi (z.1,x)) z.2 (v d)) x‖ ≤ Bnd),
      let meanA := fun z : X => incrementsActualNormalizedMean (F z.1) (hF z.1)
        (chart z.1) (fun x => L (z.1,x)) (fun x => input (z.1,x))
        (fun x => cutoff (z.1,x)) (fun x => phi (z.1,x)) (fun x => normal (z.1,x))
        (fun a x => k a (z.1,x)) tau p v i i' z.2
      let meanB := fun z : X => incrementsActualNormalizedMean (F z.1) (hF z.1)
        (chart z.1) (fun x => L (z.1,x)) (fun x => inputbar (z.1,x))
        (fun x => cutoff (z.1,x)) (fun x => phi (z.1,x)) (fun x => normal (z.1,x))
        (fun a x => kbar a (z.1,x)) tau p v i i' z.2
      let positive := O ∩ {z | 0 < L z (input z)} ∩ {z | 0 < L z (inputbar z)}
      (ContDiffOn ℝ ∞ meanA positive ∧ ContDiffOn ℝ ∞ meanB positive) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell^r * ‖iteratedFDeriv ℝ r meanA x‖ ≤ C*(tau/ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell^r * ‖iteratedFDeriv ℝ r meanB x‖ ≤ C*(tau/ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun y => meanA y-meanB y) x‖ ≤ C*(tau/ell)*Delta) ∧
      (let realA := fun y ↦ incrementsMeanRealCoordinate (meanA y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realA x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realA S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell))) ∧
      (let realB := fun y ↦ incrementsMeanRealCoordinate (meanB y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realB x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realB S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell))) ∧
      (let realDiff := fun y ↦ incrementsMeanRealCoordinate (meanA y - meanB y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realDiff x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realDiff S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell) * Delta)) := by
  classical
  choose Ce hCe hError using fun (d : J) (co : Fin N) ↦
    actual_joint_normalized_primary_error_bounds_uniform (Ep := Ep) (I := I) (M := M) j p (v d) co
      c Bnd K Bsub hc hBnd hK
  choose Cl hCl hLeading using fun (d : J) (co : Fin N) ↦
    actual_joint_normalized_primary_leading_bounds_uniform (Ep := Ep) co (v d) j c Bnd hc hBnd
  let Mcoef := ∑ a : J × Fin N, (Ce a.1 a.2 + Cl a.1 a.2)
  have hMcoef : 0 ≤ Mcoef := Finset.sum_nonneg fun a _ ↦ add_nonneg (hCe a.1 a.2) (hCl a.1 a.2)
  have hCeM (d : J) (co : Fin N) : Ce d co ≤ Mcoef :=
    (le_add_of_nonneg_right (hCl d co)).trans
      (Finset.single_le_sum (fun a _ ↦ add_nonneg (hCe a.1 a.2) (hCl a.1 a.2))
        (Finset.mem_univ (d, co)))
  have hClM (d : J) (co : Fin N) : Cl d co ≤ Mcoef :=
    (le_add_of_nonneg_left (hCe d co)).trans
      (Finset.single_le_sum (fun a _ ↦ add_nonneg (hCe a.1 a.2) (hCl a.1 a.2))
        (Finset.mem_univ (d, co)))
  let C := 6 * ‖incrementsMeanBilinear (Λ := Unit) (N := N) i i'‖ * 2 ^ j * Mcoef ^ 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A _ hCard F hF chart T _ _ O S hO hSO L input inputbar cutoff phi normal
    hL hInput hInputbar hCut hPhi
    hNormal hA hB hG hJ hT0 k kbar hk hkbar ell tau Delta hell hell1 htau htauell hDelta
    hReserve hLb hInputb hInputbarb hCutb hNormalb hInputd hAb hBb hGb hJb hT0b
    hkb hkbarb hkd hPhib
  have hEr (d : J) (co : Fin N) :=
    hError d co hCard F hF chart O S hO hSO L input inputbar cutoff phi normal
    hL hInput hInputbar hCut hPhi hNormal hA hB hG hJ hT0 k kbar hk hkbar
    ell tau Delta hell hell1 htau htauell hDelta hReserve hLb hInputb hInputbarb hCutb
    hNormalb hInputd hAb hBb hGb hJb hT0b hkb hkbarb hkd (hPhib d)
  have hLa (d : J) (co : Fin N) := hLeading d co O S hO hSO L input inputbar cutoff phi normal
    hL hInput hInputbar hCut hPhi hNormal ell Delta hell hDelta hReserve
    (fun r hr x hx ↦ hLb r (by omega) x hx)
    (fun r hr x hx ↦ hInputb r (by omega) x hx)
    (fun r hr x hx ↦ hInputbarb r (by omega) x hx)
    (fun r hr x hx ↦ hCutb r (by omega) x hx)
    (fun r hr x hx ↦ hNormalb r (by omega) x hx) (hPhib d)
    (fun r hr x hx ↦ hInputd r (by omega) x hx)
  let b := fun y : X => cutoff y*Real.sqrt (L y (input y))
  let bbar := fun y : X => cutoff y*Real.sqrt (L y (inputbar y))
  let LA : X → Unit → J → Fin N → ℂ := fun y _ d co =>
    incrementsLeadingCoefficient 1 (b y) (normal y)
      (fun a : J => fderiv ℝ (fun x => phi (y.1,x)) y.2 (v a)) d co
  let LB : X → Unit → J → Fin N → ℂ := fun y _ d co =>
    incrementsLeadingCoefficient 1 (bbar y) (normal y)
      (fun a : J => fderiv ℝ (fun x => phi (y.1,x)) y.2 (v a)) d co
  let EA : X → Unit → J → Fin N → ℂ := fun z _ d co =>
    incrementsActualNormalizedPrimaryError (F z.1) (hF z.1) (chart z.1)
      (fun x => L (z.1,x)) (fun x => input (z.1,x))
      (fun x => cutoff (z.1,x)) (fun x => phi (z.1,x)) (fun x => normal (z.1,x))
      (fun a x => k a (z.1,x)) tau p (v d) co z.2
  let EB : X → Unit → J → Fin N → ℂ := fun z _ d co =>
    incrementsActualNormalizedPrimaryError (F z.1) (hF z.1) (chart z.1)
      (fun x => L (z.1,x)) (fun x => inputbar (z.1,x))
      (fun x => cutoff (z.1,x)) (fun x => phi (z.1,x)) (fun x => normal (z.1,x))
      (fun a x => kbar a (z.1,x)) tau p (v d) co z.2
  let U := O ∩ {z | 0 < L z (input z)} ∩ {z | 0 < L z (inputbar z)}
  have hU : IsOpen U := by
    have ha : IsOpen (O ∩ {z | 0 < L z (input z)}) :=
      (hL.clm_apply hInput).continuousOn.isOpen_inter_preimage hO isOpen_Ioi
    have hb : IsOpen (O ∩ {z | 0 < L z (inputbar z)}) :=
      (hL.clm_apply hInputbar).continuousOn.isOpen_inter_preimage hO isOpen_Ioi
    convert ha.inter hb using 1
    ext z
    simp only [U,Set.mem_inter_iff,Set.mem_ofPred_eq]
    tauto
  have hSU : S ⊆ U := fun z hz =>
    ⟨⟨hSO hz,hc.trans_le (hReserve z hz).1⟩,hc.trans_le (hReserve z hz).2⟩
  have hLAs : ContDiffOn ℝ ∞ LA U := by
    apply contDiffOn_pi.2; intro u
    apply contDiffOn_pi.2; intro d
    apply contDiffOn_pi.2; intro co
    exact (hLa d co).1.1
  have hLBs : ContDiffOn ℝ ∞ LB U := by
    apply contDiffOn_pi.2; intro u
    apply contDiffOn_pi.2; intro d
    apply contDiffOn_pi.2; intro co
    exact (hLa d co).1.2
  have hEAs : ContDiffOn ℝ ∞ EA U := by
    apply contDiffOn_pi.2; intro u
    apply contDiffOn_pi.2; intro d
    apply contDiffOn_pi.2; intro co
    exact (hEr d co).1.1
  have hEBs : ContDiffOn ℝ ∞ EB U := by
    apply contDiffOn_pi.2; intro u
    apply contDiffOn_pi.2; intro d
    apply contDiffOn_pi.2; intro co
    exact (hEr d co).1.2
  have assemble (f : X → Unit → J → Fin N → ℂ) (hf : ContDiffOn ℝ ∞ f U)
      (C0 : ℝ) (hC0 : 0 ≤ C0)
      (hcomp : ∀ (u : Unit) d co, ∀ r ≤ j, ∀ x ∈ S,
        ell ^ r * ‖iteratedFDeriv ℝ r (fun y ↦ f y u d co) x‖ ≤ C0) :
      ∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r f x‖ ≤ C0 := by
    intro r hr x hx
    have hs := hf.contDiffAt (hU.mem_nhds (hSU hx))
    apply actual_joint_mean_scaled_pi f x hs r ell C0 hell hC0
    intro u
    apply actual_joint_mean_scaled_pi _ x (contDiffAt_pi.1 hs u) r ell C0 hell hC0
    intro d
    apply actual_joint_mean_scaled_pi _ x (contDiffAt_pi.1 (contDiffAt_pi.1 hs u) d)
      r ell C0 hell hC0
    intro co
    exact hcomp u d co r hr x hx
  have hLA := assemble LA hLAs Mcoef hMcoef (by
    intro u d co r hr x hx
    exact ((hLa d co).2.1 r hr x hx).trans (hClM d co))
  have hLB := assemble LB hLBs Mcoef hMcoef (by
    intro u d co r hr x hx
    exact ((hLa d co).2.2.1 r hr x hx).trans (hClM d co))
  have hEA := assemble EA hEAs (Mcoef * (tau / ell)) (by positivity) (by
    intro u d co r hr x hx
    exact ((hEr d co).2.1 r hr x hx).trans
      (mul_le_mul_of_nonneg_right (hCeM d co) (by positivity)))
  have hEB := assemble EB hEBs (Mcoef * (tau / ell)) (by positivity) (by
    intro u d co r hr x hx
    exact ((hEr d co).2.2.1 r hr x hx).trans
      (mul_le_mul_of_nonneg_right (hCeM d co) (by positivity)))
  have hLd := assemble (LA - LB) (hLAs.sub hLBs) (Mcoef * Delta) (by positivity) (by
    intro u d co r hr x hx
    exact ((hLa d co).2.2.2 r hr x hx).trans
      (mul_le_mul_of_nonneg_right (hClM d co) hDelta))
  have hEd := assemble (EA - EB) (hEAs.sub hEBs) (Mcoef * (tau / ell) * Delta)
    (by positivity) (by
    intro u d co r hr x hx
    exact ((hEr d co).2.2.2 r hr x hx).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hCeM d co) (by positivity)) hDelta))
  have heps : 0 ≤ tau / ell := by positivity
  have heps1 : tau / ell ≤ 1 := (div_le_one hell).2 htauell
  let meanA := fun y ↦ incrementsMeanRemainder (LA y) (EA y) i i'
  let meanB := fun y ↦ incrementsMeanRemainder (LB y) (EB y) i i'
  have hmean :
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r meanA x‖ ≤ C * (tau / ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r meanB x‖ ≤ C * (tau / ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
        (fun y ↦ meanA y - meanB y) x‖ ≤ C * (tau / ell) * Delta) := by
    refine ⟨?_, ?_, ?_⟩
    · intro r hr x hx
      have hres := incrementsMeanRemainder_scaled_jet U hU LA EA hLAs hEAs i i' r ell
        Mcoef (tau / ell) hell.le hMcoef heps heps1 (hSU hx)
        (fun s hs ↦ hLA s (hs.trans hr) x hx) (fun s hs ↦ hEA s (hs.trans hr) x hx)
      apply hres.trans
      dsimp [C]
      gcongr <;> norm_num
    · intro r hr x hx
      have hres := incrementsMeanRemainder_scaled_jet U hU LB EB hLBs hEBs i i' r ell
        Mcoef (tau / ell) hell.le hMcoef heps heps1 (hSU hx)
        (fun s hs ↦ hLB s (hs.trans hr) x hx) (fun s hs ↦ hEB s (hs.trans hr) x hx)
      apply hres.trans
      dsimp [C]
      gcongr <;> norm_num
    · intro r hr x hx
      have hres := incrementsMeanRemainder_difference_scaled_jet U hU LA EA LB EB
        hLAs hEAs hLBs hEBs i i' r ell Mcoef (tau / ell) Delta hell.le hMcoef
        heps heps1 hDelta (hSU hx)
        (fun s hs ↦ hLA s (hs.trans hr) x hx) (fun s hs ↦ hEB s (hs.trans hr) x hx)
        (fun s hs ↦ hLB s (hs.trans hr) x hx) (fun s hs ↦ hEA s (hs.trans hr) x hx)
        (fun s hs ↦ hLd s (hs.trans hr) x hx) (fun s hs ↦ hEd s (hs.trans hr) x hx)
      apply hres.trans
      dsimp [C]
      gcongr; norm_num

  have hmAs : ContDiffOn ℝ ∞ meanA U :=
    incrementsMeanRemainder_contDiffOn U LA EA hLAs hEAs i i'
  have hmBs : ContDiffOn ℝ ∞ meanB U :=
    incrementsMeanRemainder_contDiffOn U LB EB hLBs hEBs i i'
  have realNorm (f : X → ℂ) (hf : ContDiffOn ℝ ∞ f U) (T0 : ℝ) (hT0 : 0 ≤ T0)
      (hbound : ∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r f x‖ ≤ T0) :
      let g := fun y ↦ incrementsMeanRealCoordinate (f y)
      (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r g x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r g S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * T0 := by
    apply scaled_finiteCj_sum_le j _ S ell T0 hell hell1 hT0
    intro r hr x hx
    exact (mul_le_mul_of_nonneg_left
      (incrementsMeanRealCoordinate_jet_le f x (hf.contDiffAt (hU.mem_nhds (hSU hx))) r)
      (pow_nonneg hell.le r)).trans (hbound r hr x hx)
  dsimp only
  exact ⟨⟨hmAs,hmBs⟩,hmean.1, hmean.2.1, hmean.2.2,
    realNorm meanA hmAs _ (by dsimp [C]; positivity) hmean.1,
    realNorm meanB hmBs _ (by dsimp [C]; positivity) hmean.2.1,
    realNorm (fun y ↦ meanA y - meanB y) (hmAs.sub hmBs) _
      (by dsimp [C]; positivity) hmean.2.2⟩


end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_normalized_mean_bounds_uniform
