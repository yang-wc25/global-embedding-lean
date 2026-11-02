import Smoothing.ParameterRound2SplitCorrectionDifference
import Smoothing.ParameterRound2GlobalCorrectionIdentity
import Probes.ActualJointTensorChartTransfer
import Probes.ActualIncrementJointCorrectionDifference

/-! SAME-input difference of the original global correction through each
actual subordinate chart. Source differences enter the same finite spatial
solver; no transported R-difference or primary-error difference is supplied.
The genuine slow joint norm retains tau^2*Delta with one shifted ell power. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_actual_globalCorrection_difference_chart_transfer_split_scale
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (ν : Λ) (β : Β) (realChannel : Bool) (n length j : ℕ) (horder : j+1+length ≤ n)
    (hinverse : ∀ z ∈ (g.chart ν β).target,
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2))
    (kappa : Y → Ep × M) (U S : Set Y) (Sloc : Set X) (hU : IsOpen U) (hSU : S ⊆ U)
    (hSloc : Sloc ⊆ (g.chart ν β).target)
    (hsource : MapsTo kappa U (g.chart ν β).source)
    (hphi : ContDiffOn ℝ ∞ (fun z => g.chart ν β (kappa z)) U)
    (hmap : MapsTo (fun z => g.chart ν β (kappa z)) S Sloc)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (tau ell Mg Ks Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hKs : 0 ≤ Ks) (hDelta : 0 ≤ Delta)
    (hsrc : ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g input tau ν β) (g.chart ν β).target)
    (hsrcbar : ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g inputbar tau ν β) (g.chart ν β).target)
    (T : ℕ → ℝ) (hTnonneg : ∀ i, 0 ≤ T i)
    (hAb : ∀ k ≤ n, ∀ z ∈ Sloc, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ k ≤ n, ∀ z ∈ Sloc, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hGb : ∀ k ≤ j, ∀ z ∈ Sloc, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ k ≤ j, ∀ z ∈ Sloc, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (g.inverse ν β w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ k ≤ j, ∀ z ∈ Sloc, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hsb : ∀ k ≤ n, ∀ z ∈ Sloc, ell^k *
      ‖iteratedFDeriv ℝ k (fun w => incrementsGlobalPrimarySource F hF g input tau ν β w -
        incrementsGlobalPrimarySource F hF g inputbar tau ν β w) z‖ ≤ Ks*tau*Delta)
    (hphib : ∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ S,
      ell^(i-1) * ‖iteratedFDeriv ℝ i (fun w => g.chart ν β (kappa w)) z‖ ≤ T i) :
    let ch : (Fin (m+1) → ℂ) →L[ℝ] D :=
      if realChannel then incrementsModeRealPart else incrementsModeImagPart
    let K := actualJointHomogeneousReconstructionCost m j Mg * ‖ch‖ * Ks *
      (∑ a ∈ Finset.range length, (2*2^n*Mg)^a)
    let R := fun z => parameterRound2_globalCorrection F hF g input length tau realChannel ν β (kappa z) -
      parameterRound2_globalCorrection F hF g inputbar length tau realChannel ν β (kappa z)
    ContDiffOn ℝ ∞ R U ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^(k+1) * ‖iteratedFDeriv ℝ k R z‖ ≤
        actualFastChartTransferPrefix T j * K * tau^2 * Delta := by
  intro ch K R
  let phi := fun z => g.chart ν β (kappa z)
  let Rloc := fun z => parameterRound2_globalLocalCorrection F hF g input length tau realChannel ν β z -
    parameterRound2_globalLocalCorrection F hF g inputbar length tau realChannel ν β z
  have hell : 0 < ell := htau.trans_le htaul
  have hKg : 0 ≤ actualJointHomogeneousReconstructionCost m j Mg :=
    actualJointHomogeneousReconstructionCost_nonneg m j hMg
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hmapU : MapsTo phi U (g.chart ν β).target :=
    fun z hz => (g.chart ν β).map_source (hsource hz)
  obtain ⟨hRloc,hRjet⟩ := parameterRound2_actual_reconstructed_channel_difference_split_scale_jets F hF (g.inverse ν β)
    (incrementsGlobalPrimarySource F hF g input tau ν β)
    (incrementsGlobalPrimarySource F hF g inputbar tau ν β) ch n length j horder
    (g.chart ν β).target Sloc (g.chart ν β).open_target hSloc hA hB hG hJ hT hsrc hsrcbar
    tau ell Mg (Ks*tau*Delta) htau htaul hell1 hMg (by positivity)
    hAb hBb hGb hJb hTb hsb
  have hRloc' : ContDiffOn ℝ ∞ Rloc (g.chart ν β).target := hRloc
  have hRjet' : ∀ k ≤ j, ∀ z ∈ Sloc,
      ell^(k+1) * ‖iteratedFDeriv ℝ k Rloc z‖ ≤ K*tau^2*Delta := by
    intro k hk z hz
    exact (hRjet k hk z hz).trans_eq (by dsimp only [K]; ring)
  have heq : EqOn R (Rloc ∘ phi) U := by
    intro z hz
    exact congrArg₂ Sub.sub
      (parameterRound2_globalCorrection_eq_on_source F hF g input length tau realChannel ν β
        hinverse (kappa z) (hsource hz))
      (parameterRound2_globalCorrection_eq_on_source F hF g inputbar length tau realChannel ν β
        hinverse (kappa z) (hsource hz))
  refine ⟨(hRloc'.comp hphi hmapU).congr heq,?_⟩
  intro k hk z hz
  have hgerm : R =ᶠ[𝓝 z] Rloc ∘ phi :=
    eventuallyEq_of_mem (hU.mem_nhds (hSU hz)) (fun w hw => heq hw)
  rw [(hgerm.iteratedFDeriv ℝ k).eq_of_nhds]
  have hlocal (i : ℕ) (hi : i ≤ k) :
      ell^i * ‖iteratedFDeriv ℝ i Rloc (phi z)‖ ≤ K*tau^2*Delta/ell := by
    apply (le_div_iff₀ hell).2
    calc
      _ = ell^(i+1) * ‖iteratedFDeriv ℝ i Rloc (phi z)‖ := by rw [pow_succ]; ring
      _ ≤ _ := hRjet' i (hi.trans hk) (phi z) (hmap hz)
  have hout := actual_fast_joint_chart_transfer T hTnonneg k phi Rloc U
    (g.chart ν β).target hU (g.chart ν β).open_target hphi hRloc' hmapU z (hSU hz)
    ell ell (K*tau^2*Delta/ell) hell le_rfl hlocal
    (fun i hi hik => hphib i hi (hik.trans hk) z hz)
  calc
    ell^(k+1) * ‖iteratedFDeriv ℝ k (Rloc ∘ phi) z‖ =
        ell * (ell^k * ‖iteratedFDeriv ℝ k (Rloc ∘ phi) z‖) := by rw [pow_succ]; ring
    _ ≤ ell * (actualFastChartTransferCost T k * (K*tau^2*Delta/ell)) :=
      mul_le_mul_of_nonneg_left hout hell.le
    _ = actualFastChartTransferCost T k * K * tau^2 * Delta := by field_simp [hell.ne']
    _ ≤ actualFastChartTransferPrefix T j * K * tau^2 * Delta := by
      gcongr
      exact actualFastChartTransferCost_le_prefix T hTnonneg hk

#print axioms parameterRound2_actual_globalCorrection_difference_chart_transfer_split_scale
end GlobalEmbedding.Continuation
