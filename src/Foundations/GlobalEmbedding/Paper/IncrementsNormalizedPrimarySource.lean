import GlobalEmbedding.Paper.IncrementsModeJointSourceRegularity
import GlobalEmbedding.Paper.IncrementsSupportedAmplitudeSmoothGlue

/-!
# Actual normalized primary source: weighted size, difference and support

Original `lem:increments`, main.tex638–661. The subordinate cutoff stays INSIDE
the original free normal and source. Only observation points in its actual
support need reserve; no global source smoothness or inactive positivity is claimed.
DAG: `increments-normalized-primary-source-bounds`, exclusive W4.
-/

noncomputable section
open Manifold Set Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Paper

variable {m N : ℕ} {Ep T : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

private theorem primary_source_free_eq (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (x : D) :
    incrementsModeSource F hF c (fun _ _ _ ↦ 0) vf x =
      (2 : ℝ) • incrementsModeForcingSourcePairing
        (fun i ↦ (incrementsModeSecondForm F hF c x 0 i : V)) (vf x : V) := by
  rw [incrementsModeSource_eq_zeroFree_add, incrementsModeSource_zeroFree_eq]
  have ht : incrementsModeTransverseSource (fun _ _ _ ↦ (0 : ℝ)) x = 0 := by
    ext q
    simp [incrementsModeTransverseSource]
  rw [ht]
  change incrementsModeForcingSourceProjection (0 : Fin (m + 1) → Fin (m + 1) → ℝ) -
    incrementsModeForcingSourcePairing _ ((incrementsModeCoordinateJ F hF c x) 0 : V) + _ = _
  simp

/-- Fixed-order primitive original jets give the SAME normalized primary complex
source size and SAME-input difference, with no extra derivative loss. Both source
supports remain inside the combined original cutoffs. Tau is an external scale.
Only active observation points require reserve; original coefficient and normal
smoothness are internal inputs on O, not a supplied source estimate. -/
theorem increments_normalized_primary_source_bounds
    (j : ℕ) (c M0 MB : ℝ) (hc : 0 < c) (hM0 : 0 ≤ M0) (hMB : 0 ≤ MB) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
        (chart : Ep → D → M)
        (normal : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (chart p x))
        (O S : Set X) (_hO : IsOpen O)
        (L : X → T →L[ℝ] ℝ) (A Abar : X → T) (cp cs : X → ℝ)
        (_hSO : S ∩ tsupport (fun z ↦ cs z * cp z) ⊆ O)
        (_hL : ContDiffOn ℝ ∞ L O) (_hA : ContDiffOn ℝ ∞ A O)
        (_hAbar : ContDiffOn ℝ ∞ Abar O)
        (_hcp : ContDiffOn ℝ ∞ cp O) (_hcs : ContDiffOn ℝ ∞ cs O)
        (_hn : ContDiffOn ℝ ∞ (fun z : X ↦ (normal z.1 z.2 : V)) O)
        (_hB : ContDiffOn ℝ ∞ (fun z : X ↦ fun i : Fin (m + 1) ↦
          (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)) O)
        (ell Delta tau : ℝ) (_hell : 0 < ell) (_hDelta : 0 ≤ Delta)
        (_hreserve : ∀ x ∈ S ∩ tsupport (fun z ↦ cs z * cp z),
          c ≤ L x (A x) ∧ c ≤ L x (Abar x))
        (_hLb : ∀ i ≤ j, ∀ x ∈ S ∩ tsupport (fun z ↦ cs z * cp z),
          ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ M0)
        (_hAb : ∀ i ≤ j, ∀ x ∈ S ∩ tsupport (fun z ↦ cs z * cp z),
          ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M0)
        (_hAbarb : ∀ i ≤ j, ∀ x ∈ S ∩ tsupport (fun z ↦ cs z * cp z),
          ell ^ i * ‖iteratedFDeriv ℝ i Abar x‖ ≤ M0)
        (_hcpb : ∀ i ≤ j, ∀ x ∈ S ∩ tsupport (fun z ↦ cs z * cp z),
          ell ^ i * ‖iteratedFDeriv ℝ i cp x‖ ≤ M0)
        (_hcsb : ∀ i ≤ j, ∀ x ∈ S ∩ tsupport (fun z ↦ cs z * cp z),
          ell ^ i * ‖iteratedFDeriv ℝ i cs x‖ ≤ M0)
        (_hnb : ∀ i ≤ j, ∀ x ∈ S ∩ tsupport (fun z ↦ cs z * cp z),
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z : X ↦ (normal z.1 z.2 : V)) x‖ ≤ M0)
        (_hBb : ∀ i ≤ j, ∀ x ∈ S ∩ tsupport (fun z ↦ cs z * cp z),
          ell ^ i * ‖iteratedFDeriv ℝ i
          (fun z : X ↦ fun a : Fin (m + 1) ↦
            (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 a : V)) x‖ ≤ MB)
        (_hdiff : ∀ i ≤ j, ∀ x ∈ S ∩ tsupport (fun z ↦ cs z * cp z),
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z ↦ A z - Abar z) x‖ ≤ Delta),
      let vf := fun (B : X → T) (p : Ep) (x : D) ↦
        cs (p, x) • ((Real.sqrt 2 * 1 * tau * (cp (p, x) *
          Real.sqrt (L (p, x) (B (p, x))))) • normal p x)
      let k := fun (B : X → T) (z : X) ↦ incrementsModeComplexInclude
        (incrementsModeSource (F z.1) (hF z.1) (chart z.1)
          (fun _ _ _ ↦ 0) (vf B z.1) z.2)
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r (k A) x‖ ≤ K * |tau|) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r *
        ‖iteratedFDeriv ℝ r (fun z ↦ k A z - k Abar z) x‖ ≤ K * |tau| * Delta) ∧
      tsupport (k A) ⊆ tsupport (fun z ↦ cs z * cp z) ∧
      tsupport (k Abar) ⊆ tsupport (fun z ↦ cs z * cp z) := by
  let Mamp := max M0 (2 ^ j * M0 * M0)
  have hMamp : 0 ≤ Mamp := le_trans hM0 (le_max_left _ _)
  obtain ⟨Cs, hCs, hsize⟩ :=
    increments_positive_reserve_amplitude_scaled_jets j c Mamp hc hMamp
  obtain ⟨Cd, hCd, hdiff⟩ :=
    increments_positive_reserve_amplitude_difference_scaled_jets j c Mamp hc hMamp
  let C := max Cs Cd
  let Q := incrementsModeForcingSourcePairing (m := m) (N := N)
  let J := incrementsModeComplexInclude (m := m)
  refine ⟨2 * 2 ^ j * ‖J‖ * ‖Q‖ * MB * (Real.sqrt 2 * C), by
    dsimp [C]; positivity, ?_⟩
  intro F hF chart normal O S hO L A Abar cp cs hSO hL hA hAbar hcp hcs hn hB
    ell Delta tau hell hDelta hreserve hLb hAb hAbarb hcpb hcsb hnb hBb hAB vf k
  let eta : X → ℝ := fun z ↦ cs z * cp z
  let nV : X → V := fun z ↦ (normal z.1 z.2 : V)
  let w := fun (B : X → T) (z : X) ↦ (eta z * Real.sqrt (L z (B z))) • nV z
  let Brow := fun z : X ↦ fun a : Fin (m + 1) ↦
    (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 a : V)
  let q := fun z : X ↦ Q (Brow z)
  let s := 2 * Real.sqrt 2 * tau
  have hq : ContDiffOn ℝ ∞ q O := Q.contDiff.comp_contDiffOn hB
  have heta : ContDiffOn ℝ ∞ eta O := hcs.mul hcp
  have hformula (B : X → T) (z : X) : k B z = s • J (q z (w B z)) := by
    dsimp only [k]
    rw [primary_source_free_eq]
    simp only [map_smul, vf, Submodule.coe_smul_of_tower, smul_smul]
    dsimp [s, w, eta, nV, q, Q, J, Brow]
    simp only [map_smul, smul_smul]
    congr 1
    ring
  have hzero (B : X → T) {x : X} (hx : x ∉ tsupport eta) :
      k B =ᶠ[𝓝 x] (fun _ ↦ (0 : Fin (m + 1) → ℂ)) := by
    filter_upwards [increments_supported_amplitude_eventually_zero L B eta nV hx] with z hz
    rw [hformula, show w B z = 0 from hz]
    simp
  have hsupport (B : X → T) : tsupport (k B) ⊆ tsupport eta := by
    apply closure_minimal _ (isClosed_tsupport eta)
    intro x hx
    by_contra hn
    exact hx ((hzero B hn).self_of_nhds)
  have hetab : ∀ i ≤ j, ∀ x ∈ S ∩ tsupport eta,
      ell ^ i * ‖iteratedFDeriv ℝ i eta x‖ ≤ Mamp := by
    intro i hi x hx
    let mulR := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
    have hm : ContDiffOn ℝ ∞ (fun z ↦ mulR (cs z)) O :=
      mulR.contDiff.comp_contDiffOn hcs
    have hmb (r : ℕ) (hr : r ≤ i) :
        ell ^ r * ‖iteratedFDeriv ℝ r (fun z ↦ mulR (cs z)) x‖ ≤ M0 := by
      calc
        _ ≤ ell ^ r * (‖mulR‖ * ‖iteratedFDeriv ℝ r cs x‖) :=
          mul_le_mul_of_nonneg_left (mulR.norm_iteratedFDeriv_comp_left
            (hcs.contDiffAt (hO.mem_nhds (hSO hx))) (by simp)) (by positivity)
        _ ≤ ell ^ r * (1 * ‖iteratedFDeriv ℝ r cs x‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_lsmul_le
        _ ≤ M0 := by simpa using hcsb r (hr.trans hi) x hx
    have hb := scaled_clm_apply O hO (fun z ↦ mulR (cs z)) cp hm hcp i 0 ell M0 M0
      hell.le hmb (fun r hr ↦ by simpa using hcpb r (hr.trans hi) x hx) (hSO hx)
    calc
      _ ≤ 2 ^ i * M0 * M0 := by simpa [eta, mulR, smul_eq_mul] using hb
      _ ≤ 2 ^ j * M0 * M0 := by gcongr; norm_num
      _ ≤ Mamp := le_max_right _ _
  let Sa := S ∩ tsupport eta
  have hSa : Sa ⊆ O := hSO
  have hwa := hsize O Sa hO hSa L A eta nV hL hA heta hn ell hell
    (fun x hx ↦ (hreserve x hx).1)
    (fun i hi x hx ↦ (hLb i hi x hx).trans (le_max_left _ _))
    (fun i hi x hx ↦ (hAb i hi x hx).trans (le_max_left _ _))
    (fun i hi x hx ↦ hetab i hi x hx)
    (fun i hi x hx ↦ (hnb i hi x hx).trans (le_max_left _ _))
  have hwab := hdiff O Sa hO hSa L A Abar eta nV hL hA hAbar heta hn
    ell Delta hell hDelta hreserve
    (fun i hi x hx ↦ (hLb i hi x hx).trans (le_max_left _ _))
    (fun i hi x hx ↦ (hAb i hi x hx).trans (le_max_left _ _))
    (fun i hi x hx ↦ (hAbarb i hi x hx).trans (le_max_left _ _))
    (fun i hi x hx ↦ hetab i hi x hx)
    (fun i hi x hx ↦ (hnb i hi x hx).trans (le_max_left _ _))
    (fun i hi x hx ↦ hAB i hi x hx)
  let P := O ∩ {z | 0 < L z (A z)} ∩ {z | 0 < L z (Abar z)}
  have hP : IsOpen P := by
    have ha : IsOpen (O ∩ {z | 0 < L z (A z)}) :=
      (hL.clm_apply hA).continuousOn.isOpen_inter_preimage hO isOpen_Ioi
    have hb : IsOpen (O ∩ {z | 0 < L z (Abar z)}) :=
      (hL.clm_apply hAbar).continuousOn.isOpen_inter_preimage hO isOpen_Ioi
    convert ha.inter hb using 1
    ext z
    simp [P, and_assoc, and_left_comm]
  have hPO : P ⊆ O := fun _ hz ↦ hz.1.1
  have hwaP : ContDiffOn ℝ ∞ (w A) P :=
    ((heta.mono hPO).mul (((hL.clm_apply hA).mono hPO).sqrt
      (fun _ hz ↦ hz.1.2.ne'))).smul (hn.mono hPO)
  have hwbP : ContDiffOn ℝ ∞ (w Abar) P :=
    ((heta.mono hPO).mul (((hL.clm_apply hAbar).mono hPO).sqrt
      (fun _ hz ↦ hz.2.ne'))).smul (hn.mono hPO)
  have hqb (r : ℕ) (hr : r ≤ j) (x : X) (hx : x ∈ Sa) :
      ell ^ r * ‖iteratedFDeriv ℝ r q x‖ ≤ ‖Q‖ * MB := by
    calc
      _ ≤ ell ^ r * (‖Q‖ * ‖iteratedFDeriv ℝ r Brow x‖) :=
        mul_le_mul_of_nonneg_left (Q.norm_iteratedFDeriv_comp_left
          (hB.contDiffAt (hO.mem_nhds (hSO hx))) (by simp)) (by positivity)
      _ = ‖Q‖ * (ell ^ r * ‖iteratedFDeriv ℝ r Brow x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hBb r hr x hx) (norm_nonneg Q)
  have hbound (f : X → V) (hf : ContDiffOn ℝ ∞ f P) (R : ℝ) (hR : 0 ≤ R)
      (r : ℕ) (hr : r ≤ j) (x : X) (hx : x ∈ Sa)
      (hb : ∀ i ≤ r, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ C * R) :
      ell ^ r * ‖iteratedFDeriv ℝ r (fun z ↦ s • J (q z (f z))) x‖ ≤
        (2 * 2 ^ j * ‖J‖ * ‖Q‖ * MB * (Real.sqrt 2 * C)) * |tau| * R := by
    have hxP : x ∈ P := ⟨⟨hSa hx, hc.trans_le (hreserve x hx).1⟩,
      hc.trans_le (hreserve x hx).2⟩
    have hp := scaled_clm_apply P hP q f (hq.mono hPO) hf r 0 ell (‖Q‖ * MB)
      (C * R) hell.le (fun i hi ↦ hqb i (hi.trans hr) x hx)
      (fun i hi ↦ by simpa using hb i hi) hxP
    have hg := (hq.mono hPO).clm_apply hf
    have hj : ContDiffAt ℝ ∞ (fun z ↦ J (q z (f z))) x :=
      J.contDiff.contDiffAt.comp x (hg.contDiffAt (hP.mem_nhds hxP))
    rw [iteratedFDeriv_const_smul_apply' (hj.of_le (by simp)), norm_smul,
      Real.norm_eq_abs]
    calc
      _ ≤ |s| * (‖J‖ * (2 ^ r * (‖Q‖ * MB) * (C * R))) := by
        have hbJ := J.norm_iteratedFDeriv_comp_left
          (hg.contDiffAt (hP.mem_nhds hxP)) (n := r) (by simp)
        have hp' : ell ^ r * ‖iteratedFDeriv ℝ r (fun z ↦ J (q z (f z))) x‖ ≤
            ‖J‖ * (2 ^ r * (‖Q‖ * MB) * (C * R)) := by
          calc
            _ ≤ ell ^ r * (‖J‖ * ‖iteratedFDeriv ℝ r (fun z ↦ q z (f z)) x‖) :=
              mul_le_mul_of_nonneg_left hbJ (by positivity)
            _ = ‖J‖ * (ell ^ r * ‖iteratedFDeriv ℝ r (fun z ↦ q z (f z)) x‖) := by
              ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa using hp) (norm_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hp' (abs_nonneg s)]
      _ ≤ |s| * (‖J‖ * (2 ^ j * (‖Q‖ * MB) * (C * R))) := by
        dsimp [C]
        gcongr
        norm_num
      _ = _ := by
        simp only [s, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
          abs_of_nonneg (Real.sqrt_nonneg 2)]
        ring
  refine ⟨?_, ?_, hsupport A, hsupport Abar⟩
  · intro r hr x hx
    by_cases hs : x ∈ tsupport eta
    · have hb := hbound (w A) hwaP 1 (by norm_num) r hr x ⟨hx, hs⟩
        (fun i hi ↦ by
          simpa only [mul_one] using
            (hwa i (hi.trans hr) x ⟨hx, hs⟩).trans (le_max_left Cs Cd))
      simp only [mul_one] at hb
      simpa only [show k A = (fun z ↦ s • J (q z (w A z))) from funext (hformula A)]
        using hb
    · rw [((hzero A hs).iteratedFDeriv (𝕜 := ℝ) r).self_of_nhds,
        iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
      positivity
  · intro r hr x hx
    have heq : (fun z ↦ k A z - k Abar z) =
        (fun z ↦ s • J (q z (w A z - w Abar z))) := by
      funext z
      simp only [hformula, map_sub, smul_sub]
    by_cases hs : x ∈ tsupport eta
    · rw [heq]
      apply hbound (fun z ↦ w A z - w Abar z) (hwaP.sub hwbP) Delta hDelta r hr x
        ⟨hx, hs⟩
      intro i hi
      exact (hwab i (hi.trans hr) x ⟨hx, hs⟩).trans
        (mul_le_mul_of_nonneg_right (le_max_right Cs Cd) hDelta)
    · have hz : (fun z ↦ k A z - k Abar z) =ᶠ[𝓝 x]
          (fun _ ↦ (0 : Fin (m + 1) → ℂ)) := by
        filter_upwards [hzero A hs, hzero Abar hs] with z ha hb
        simp only [ha, hb, sub_zero]
      rw [(hz.iteratedFDeriv (𝕜 := ℝ) r).self_of_nhds, iteratedFDeriv_fun_zero,
        Pi.zero_apply, norm_zero, mul_zero]
      positivity

end GlobalEmbedding.Paper
