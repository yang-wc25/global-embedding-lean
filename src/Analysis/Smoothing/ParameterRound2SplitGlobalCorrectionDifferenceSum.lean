import Smoothing.ParameterRound2SplitGlobalCorrectionDifference
import Smoothing.ParameterRound2GlobalCorrectionSupport

/-! SAME-input difference of the literal global same-phase correction sum.
Each subordinate keeps its own adapted chart and finite solver. Original
combined-cutoff support is independent of the varying tensor, so both terms
have the same local active set. Source differences produce tau^2*Delta after
actual transport and the true subordinate multiplicity. -/

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

theorem parameterRound2_actual_globalCorrection_difference_sum_split_scale
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (ν : Λ) (realChannel : Bool) (n length j Rsub : ℕ) (horder : j+1+length ≤ n)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hsupport : ∀ β, incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ (g.chart ν β).source)
    (hinverse : ∀ β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2))
    (kappa : Y → Ep × M) (Omega S : Set Y) (U : Β → Set Y) (Sloc : Β → Set X)
    (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmapW : MapsTo kappa Omega W)
    (hU : ∀ β, IsOpen (U β))
    (hOU : ∀ β, Omega ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ U β)
    (hSloc : ∀ β, Sloc β ⊆ (g.chart ν β).target)
    (hsource : ∀ β, MapsTo kappa (U β) (g.chart ν β).source)
    (hphi : ∀ β, ContDiffOn ℝ ∞ (fun z => g.chart ν β (kappa z)) (U β))
    (hmap : ∀ β, MapsTo (fun z => g.chart ν β (kappa z))
      (S ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W (fun z => g.eta ν β z*g.cutoff ν z)) (Sloc β))
    (hA : ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hB : ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hG : ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hJ : ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hT : ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (tau ell Mg Ks Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hKs : 0 ≤ Ks) (hDelta : 0 ≤ Delta)
    (hsrc : ∀ β, ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g input tau ν β) (g.chart ν β).target)
    (hsrcbar : ∀ β, ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g inputbar tau ν β) (g.chart ν β).target)
    (T : ℕ → ℝ) (hTnonneg : ∀ i, 0 ≤ T i)
    (hAb : ∀ β k, k ≤ n → ∀ z ∈ Sloc β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ β k, k ≤ n → ∀ z ∈ Sloc β, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hGb : ∀ β k, k ≤ j → ∀ z ∈ Sloc β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ β k, k ≤ j → ∀ z ∈ Sloc β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (g.inverse ν β w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ β k, k ≤ j → ∀ z ∈ Sloc β, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hsb : ∀ β k, k ≤ n → ∀ z ∈ Sloc β, ell^k *
      ‖iteratedFDeriv ℝ k (fun w => incrementsGlobalPrimarySource F hF g input tau ν β w -
        incrementsGlobalPrimarySource F hF g inputbar tau ν β w) z‖ ≤ Ks*tau*Delta)
    (hphib : ∀ β i, 1 ≤ i → i ≤ j → ∀ z ∈ S ∩ kappa ⁻¹'
      incrementsGlobalRelativeSupport W (fun w => g.eta ν β w*g.cutoff ν w),
      ell^(i-1) * ‖iteratedFDeriv ℝ i (fun w => g.chart ν β (kappa w)) z‖ ≤ T i)
    (hRsub : ∀ z ∈ S, (Finset.univ.filter (fun β => kappa z ∈
      incrementsGlobalRelativeSupport W (fun w => g.eta ν β w*g.cutoff ν w))).card ≤ Rsub) :
    let ch : (Fin (m+1) → ℂ) →L[ℝ] D :=
      if realChannel then incrementsModeRealPart else incrementsModeImagPart
    let K := actualFastChartTransferPrefix T j *
      (actualJointHomogeneousReconstructionCost m j Mg * ‖ch‖ * Ks *
        (∑ a ∈ Finset.range length, (2*2^n*Mg)^a))
    let Rsum := fun z : Y => (∑ β,
      parameterRound2_globalCorrection F hF g input length tau realChannel ν β (kappa z)) -
      (∑ β, parameterRound2_globalCorrection F hF g inputbar length tau realChannel ν β (kappa z))
    ContDiffOn ℝ ∞ Rsum Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^(k+1) * ‖iteratedFDeriv ℝ k Rsum z‖ ≤ (Rsub:ℝ)*K*tau^2*Delta := by
  intro ch K Rsum
  let Ksupport := fun β => incrementsGlobalRelativeSupport W (fun z => g.eta ν β z*g.cutoff ν z)
  let f := fun β z => parameterRound2_globalCorrection F hF g input length tau realChannel ν β z -
    parameterRound2_globalCorrection F hF g inputbar length tau realChannel ν β z
  have hs (β) : tsupport (fun z : W => f β z) ⊆ Subtype.val ⁻¹' Ksupport β := by
    have h1 := parameterRound2_globalCorrection_relative_support F hF g input length tau realChannel ν β
      W hW (hsupport β) (hinverse β)
    have h2 := parameterRound2_globalCorrection_relative_support F hF g inputbar length tau realChannel ν β
      W hW (hsupport β) (hinverse β)
    exact (tsupport_sub _ _).trans (Set.union_subset h1 h2)
  have hper (β) := parameterRound2_actual_globalCorrection_difference_chart_transfer_split_scale F hF g input inputbar ν β
    realChannel n length j horder (hinverse β) kappa (U β) (S ∩ kappa ⁻¹' Ksupport β)
    (Sloc β) (hU β) (fun z hz => hOU β ⟨hSOmega hz.1,hz.2⟩)
    (hSloc β) (hsource β) (hphi β) (hmap β) (hA β) (hB β) (hG β) (hJ β) (hT β)
    tau ell Mg Ks Delta htau htaul hell1 hMg hKs hDelta (hsrc β) (hsrcbar β) T hTnonneg
    (hAb β) (hBb β) (hGb β) (hJb β) (hTb β) (hsb β) (hphib β)
  have hKg : 0 ≤ actualJointHomogeneousReconstructionCost m j Mg :=
    actualJointHomogeneousReconstructionCost_nonneg m j hMg
  have hKtr : 0 ≤ actualFastChartTransferPrefix T j := actualFastChartTransferPrefix_nonneg T hTnonneg j
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hout := parameterRound2_relative_supported_sum_weighted_jets f W Ksupport hW hs
    kappa Omega S hOmega hSOmega hkappa hmapW U hU hOU (fun β => (hper β).1)
    Rsub j 1 hRsub ell (K*tau^2*Delta) (htau.trans_le htaul) (by positivity)
    (fun β k hk z hz => (hper β).2 k hk z hz)
  have heq : (fun z => ∑ β, f β (kappa z)) = Rsum := by
    funext z
    simp only [Rsum,f,Finset.sum_sub_distrib]
  rw [heq] at hout
  refine ⟨hout.1,?_⟩
  intro k hk z hz
  simpa only [mul_assoc] using hout.2 k hk z hz

#print axioms parameterRound2_actual_globalCorrection_difference_sum_split_scale
end GlobalEmbedding.Continuation
