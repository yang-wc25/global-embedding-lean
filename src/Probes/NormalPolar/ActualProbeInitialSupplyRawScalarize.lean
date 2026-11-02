import Smoothing.ParameterRound2MeanRawProfiles
import Smoothing.WeightedActualOperations

/-! A genuine scalar representation of the same produced background input.
The original local and observed linear functionals are applied to their
actual tensors.  This keeps every chart, sampling set, physical input and
geometric profile, and obtains the product bounds before any use of the
reconstructed wave.  The comparison input is the same input, so its true
difference is zero. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def actualProbeRawScalarCost (n j : ℕ) (Bnd : ℝ) : ℝ :=
  1+Bnd+2^n*Bnd^2+2^(j+1)*Bnd^2

theorem actualProbeRawScalarCost_nonneg (n j : ℕ) (Bnd : ℝ) (hBnd : 0 ≤ Bnd) :
    0 ≤ actualProbeRawScalarCost n j Bnd := by
  unfold actualProbeRawScalarCost
  positivity

def actualProbeInitialSupply_raw_scalarize
    (n length j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (hBnd : 0 ≤ Bnd) (T : ℕ → ℝ)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (e : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ)
    (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
      reserve Bnd Mg T F hF g input inputbar W primary e O S tau ell Delta) :
    ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lprimary
      reserve (actualProbeRawScalarCost n j Bnd) Mg T
      F hF g input input W primary e O S tau ell 0 := by
  let C := actualProbeRawScalarCost n j Bnd
  have hLocal : 0 ≤ (2:ℝ)^n*Bnd^2 := by positivity
  have hObs : 0 ≤ (2:ℝ)^(j+1)*Bnd^2 := by positivity
  have h1 : 1 ≤ C := by dsimp [C,actualProbeRawScalarCost]; linarith
  have hB : Bnd ≤ C := by dsimp [C,actualProbeRawScalarCost]; linarith
  have hLC : (2:ℝ)^n*Bnd^2 ≤ C := by dsimp [C,actualProbeRawScalarCost]; linarith
  have hOC : (2:ℝ)^(j+1)*Bnd^2 ≤ C := by dsimp [C,actualProbeRawScalarCost]; linarith
  have hell : 0 ≤ ell := (data.htau.trans_le data.htaul).le
  have hId (k : ℕ) (z : X) :
      ell^k*‖iteratedFDeriv ℝ k (fun _ : X => ContinuousLinearMap.id ℝ ℝ) z‖ ≤ C := by
    by_cases hk : k = 0
    · subst k
      simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ)).trans h1
    · rw [iteratedFDeriv_const_of_ne hk]
      simpa using zero_le_one.trans h1
  have hlocal (nu : Λ) (beta : Β) (k : ℕ) (hk : k ≤ n) (z : X)
      (hz : z ∈ data.Sloc nu beta) :
      ell^k*‖iteratedFDeriv ℝ k (fun w => data.L nu beta w (data.A nu beta w)) z‖ ≤ C := by
    have hb := scaled_clm_apply (g.chart nu beta).target (g.chart nu beta).open_target
      (data.L nu beta) (data.A nu beta) (data.hL nu beta) (data.hInput nu beta)
      k 0 ell Bnd Bnd hell
      (fun a ha => data.hLb nu beta a (ha.trans hk) z hz)
      (fun a ha => by simpa only [Nat.add_zero] using data.hInputb nu beta a (ha.trans hk) z hz)
      (data.hSloc nu beta hz)
    simp only [Nat.add_zero] at hb
    apply hb.trans
    calc
      (2:ℝ)^k*Bnd*Bnd = 2^k*Bnd^2 := by ring
      _ ≤ 2^n*Bnd^2 := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk) (sq_nonneg _)
      _ ≤ C := hLC
  have hobs (nu : Λ) (k : ℕ) (hk : k ≤ j+1) (z : X)
      (hz : z ∈ S ∩ (fun w : X => (w.1,e.symm w.2)) ⁻¹'
        incrementsGlobalRelativeSupport W (g.cutoff nu)) :
      ell^k*‖iteratedFDeriv ℝ k (fun w => data.Lobs nu w (data.Aobs nu w)) z‖ ≤ C := by
    have hb := scaled_clm_apply (data.Omega nu) (data.hOmega nu)
      (data.Lobs nu) (data.Aobs nu) (data.hLobs nu) (data.hAobs nu)
      k 0 ell Bnd Bnd hell
      (fun a ha => data.hLobsb nu a (ha.trans hk) z hz)
      (fun a ha => by simpa only [Nat.add_zero] using data.hAobsb nu a (ha.trans hk) z hz)
      (data.hSOmega nu hz)
    simp only [Nat.add_zero] at hb
    apply hb.trans
    calc
      (2:ℝ)^k*Bnd*Bnd = 2^k*Bnd^2 := by ring
      _ ≤ 2^(j+1)*Bnd^2 := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk) (sq_nonneg _)
      _ ≤ C := hOC
  exact {
    prim := data.prim
    primbar := data.prim
    hO := data.hO
    hSO := data.hSO
    hkappaO := data.hkappaO
    hmapWO := data.hmapWO
    Omega := data.Omega
    U := data.U
    Sloc := data.Sloc
    hOmega := data.hOmega
    hSOmega := data.hSOmega
    hkappa := data.hkappa
    hmapW := data.hmapW
    hU := data.hU
    hOU := data.hOU
    hSloc := data.hSloc
    hsource := data.hsource
    hphi := data.hphi
    hmap := data.hmap
    htau := data.htau
    htaul := data.htaul
    hell1 := data.hell1
    hDelta := le_rfl
    L := fun _ _ _ => ContinuousLinearMap.id ℝ ℝ
    A := fun nu beta z => data.L nu beta z (data.A nu beta z)
    Abar := fun nu beta z => data.L nu beta z (data.A nu beta z)
    hL := fun _ _ => contDiffOn_const
    hInput := fun nu beta => (data.hL nu beta).clm_apply (data.hInput nu beta)
    hInputbar := fun nu beta => (data.hL nu beta).clm_apply (data.hInput nu beta)
    hRep := data.hRep
    hRepbar := data.hRep
    hCut := data.hCut
    hEta := data.hEta
    hNormal := data.hNormal
    hBR := data.hBR
    hReserve := fun nu beta z hz => ⟨(data.hReserve nu beta z hz).1,(data.hReserve nu beta z hz).1⟩
    hBRb := fun nu beta k hk z hz => (data.hBRb nu beta k hk z hz).trans hB
    hLb := fun _ _ k _ z _ => hId k z
    hInputb := hlocal
    hInputbarb := hlocal
    hCutb := fun nu beta k hk z hz => (data.hCutb nu beta k hk z hz).trans hB
    hEtab := fun nu beta k hk z hz => (data.hEtab nu beta k hk z hz).trans hB
    hNormalb := fun nu beta k hk z hz => (data.hNormalb nu beta k hk z hz).trans hB
    hDiff := by intro nu beta k hk z hz; simp
    hAb := data.hAb
    hBb := data.hBb
    hGb := data.hGb
    hJb := data.hJb
    hTb := data.hTb
    hphib := data.hphib
    hRsub := data.hRsub
    Lobs := fun _ _ => ContinuousLinearMap.id ℝ ℝ
    Aobs := fun nu z => data.Lobs nu z (data.Aobs nu z)
    Abarobs := fun nu z => data.Lobs nu z (data.Aobs nu z)
    hLobs := fun _ => contDiffOn_const
    hAobs := fun nu => (data.hLobs nu).clm_apply (data.hAobs nu)
    hAbarobs := fun nu => (data.hLobs nu).clm_apply (data.hAobs nu)
    hRepobs := data.hRepobs
    hRepbarobs := data.hRepobs
    hCutobs := data.hCutobs
    hNormalobs := data.hNormalobs
    hPhaseobs := data.hPhaseobs
    hReserveobs := fun nu z hz => ⟨(data.hReserveobs nu z hz).1,(data.hReserveobs nu z hz).1⟩
    hLobsb := fun _ k _ z _ => hId k z
    hAobsb := hobs
    hAbarobsb := hobs
    hCutobsb := fun nu k hk z hz => (data.hCutobsb nu k hk z hz).trans hB
    hNormalobsb := fun nu k hk z hz => (data.hNormalobsb nu k hk z hz).trans hB
    hGradobsb := fun nu r k hk z hz => (data.hGradobsb nu r k hk z hz).trans hB
    hDiffobs := by intro nu k hk z hz; simp
    hCover := data.hCover
    hPositiveCover := fun nu z hz => ⟨(data.hPositiveCover nu z hz).1,(data.hPositiveCover nu z hz).1⟩
    hCount := data.hCount }

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeRawScalarCost_nonneg
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_raw_scalarize
