import Smoothing.ParameterRound2SourceDifferenceIndex
import Smoothing.ParameterRound2SplitGlobalCorrectionDifferenceSum
import Smoothing.ParameterRound2SplitGlobalCorrectionSum
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep Y Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_actual_primitive_globalCorrection_sum_uniform_split_scale_index
    (n length j Rsub : ℕ) (horder : j+1+length ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hTnonneg : ∀ i, 0 ≤ T i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β]
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (ν : Λ) (realChannel : Bool)
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
    (tau ell Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hDelta : 0 ≤ Delta)
    (hsrc : ∀ β, ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g input tau ν β) (g.chart ν β).target)
    (hsrcbar : ∀ β, ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g inputbar tau ν β) (g.chart ν β).target)
    (L : Β → X → Tr →L[ℝ] ℝ) (A Abar : Β → X → Tr)
    (hL : ∀ β, ContDiffOn ℝ ∞ (L β) (g.chart ν β).target)
    (hInput : ∀ β, ContDiffOn ℝ ∞ (A β) (g.chart ν β).target)
    (hInputbar : ∀ β, ContDiffOn ℝ ∞ (Abar β) (g.chart ν β).target)
    (hRep : ∀ β z, z ∈ (g.chart ν β).target → L β z (A β z) =
      g.linearArgument ν z.1 (g.inverse ν β z.1 z.2) (input z.1 (g.inverse ν β z.1 z.2)))
    (hRepbar : ∀ β z, z ∈ (g.chart ν β).target → L β z (Abar β z) =
      g.linearArgument ν z.1 (g.inverse ν β z.1 z.2) (inputbar z.1 (g.inverse ν β z.1 z.2)))
    (hCut : ∀ β, ContDiffOn ℝ ∞ (fun z : X => g.cutoff ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
    (hEta : ∀ β, ContDiffOn ℝ ∞ (fun z : X => g.eta ν β (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
    (hNormal : ∀ β, ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
    (hBR : ∀ β, ContDiffOn ℝ ∞ (fun z : X => fun a : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 a : V)) (g.chart ν β).target)
    (hReserve : ∀ β z, z ∈ Sloc β → c ≤ L β z (A β z) ∧ c ≤ L β z (Abar β z))
    (hBRb : ∀ β r, r ≤ n → ∀ z ∈ Sloc β, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => fun a : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (g.inverse ν β w.1) w.2 0 a : V)) z‖ ≤ Bnd)
    (hLb : ∀ β r, r ≤ n → ∀ z ∈ Sloc β, ell^r * ‖iteratedFDeriv ℝ r (L β) z‖ ≤ Bnd)
    (hInputb : ∀ β r, r ≤ n → ∀ z ∈ Sloc β, ell^r * ‖iteratedFDeriv ℝ r (A β) z‖ ≤ Bnd)
    (hInputbarb : ∀ β r, r ≤ n → ∀ z ∈ Sloc β, ell^r * ‖iteratedFDeriv ℝ r (Abar β) z‖ ≤ Bnd)
    (hCutb : ∀ β r, r ≤ n → ∀ z ∈ Sloc β, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => g.cutoff ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
    (hEtab : ∀ β r, r ≤ n → ∀ z ∈ Sloc β, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => g.eta ν β (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
    (hNormalb : ∀ β r, r ≤ n → ∀ z ∈ Sloc β, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => g.normal ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
    (hDiff : ∀ β r, r ≤ n → ∀ z ∈ Sloc β, ell^r * ‖iteratedFDeriv ℝ r
      (fun w => A β w-Abar β w) z‖ ≤ Delta)
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
    (hphib : ∀ β i, 1 ≤ i → i ≤ j → ∀ z ∈ S ∩ kappa ⁻¹'
      incrementsGlobalRelativeSupport W (fun w => g.eta ν β w*g.cutoff ν w),
      ell^(i-1) * ‖iteratedFDeriv ℝ i (fun w => g.chart ν β (kappa w)) z‖ ≤ T i)
    (hRsub : ∀ z ∈ S, (Finset.univ.filter (fun β => kappa z ∈
      incrementsGlobalRelativeSupport W (fun w => g.eta ν β w*g.cutoff ν w))).card ≤ Rsub),
    let RsumA := fun z : Y => ∑ β,
      parameterRound2_globalCorrection F hF g input length tau realChannel ν β (kappa z)
    let RsumB := fun z : Y => ∑ β,
      parameterRound2_globalCorrection F hF g inputbar length tau realChannel ν β (kappa z)
    (ContDiffOn ℝ ∞ RsumA Omega ∧ ContDiffOn ℝ ∞ RsumB Omega) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k RsumA z‖ ≤ K*tau^2) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k RsumB z‖ ≤ K*tau^2) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k (fun w => RsumA w-RsumB w) z‖ ≤ K*tau^2*Delta) := by
  obtain ⟨Ka,hKa,hsize⟩ := parameterRound2_actual_original_source_jets_uniform_index
    (I := I) (M := M) (Ep := Ep) (T := Tr) (m := m) (N := N) n c Bnd hc hBnd
  obtain ⟨Kd,hKd,hdiff⟩ := parameterRound2_actual_original_source_difference_jets_uniform_index
    (I := I) (M := M) (Ep := Ep) (T := Tr) (m := m) (N := N) n c Bnd hc hBnd
  let Ks := max Ka Kd
  have hKs : 0 ≤ Ks := hKa.trans (le_max_left _ _)
  let Kch := ‖incrementsModeRealPart (m := m)‖+‖incrementsModeImagPart (m := m)‖
  have hKch : 0 ≤ Kch := add_nonneg (norm_nonneg _) (norm_nonneg _)
  let K := (Rsub:ℝ)*actualFastChartTransferPrefix T j*
    (actualJointHomogeneousReconstructionCost m j Mg*Kch*Ks*
      (∑ a ∈ Finset.range length, (2*2^n*Mg)^a))
  have hKr := actualJointHomogeneousReconstructionCost_nonneg m j hMg
  have hKtr := actualFastChartTransferPrefix_nonneg T hTnonneg j
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro Λ Β _ _ F hF g input inputbar ν realChannel W hW hsupport hinverse kappa Omega S U Sloc
    hOmega hSOmega hkappa hmapW hU hOU hSloc hsource hphi hmap hA hB hG hJ hT
    tau ell Delta htau htaul hell1 hDelta hsrc hsrcbar
    L A Abar hL hInput hInputbar hRep hRepbar hCut hEta hNormal hBR hReserve
    hBRb hLb hInputb hInputbarb hCutb hEtab hNormalb hDiff
    hAb hBb hGb hJb hTb hphib hRsub RsumA RsumB
  have hell : 0 < ell := htau.trans_le htaul
  have hsA (β) := hsize F hF g input ν β (Sloc β) (hSloc β) (L β) (A β)
    (hL β) (hInput β) (hRep β) (hCut β) (hEta β) (hNormal β) (hBR β)
    ell tau hell htau.le (fun z hz => (hReserve β z hz).1) (hBRb β) (hLb β)
    (hInputb β) (hCutb β) (hEtab β) (hNormalb β)
  have hsB (β) := hsize F hF g inputbar ν β (Sloc β) (hSloc β) (L β) (Abar β)
    (hL β) (hInputbar β) (hRepbar β) (hCut β) (hEta β) (hNormal β) (hBR β)
    ell tau hell htau.le (fun z hz => (hReserve β z hz).2) (hBRb β) (hLb β)
    (hInputbarb β) (hCutb β) (hEtab β) (hNormalb β)
  have hsD (β) := hdiff F hF g input inputbar ν β (Sloc β) (hSloc β) (L β) (A β) (Abar β)
    (hL β) (hInput β) (hInputbar β) (hRep β) (hRepbar β) (hCut β) (hEta β) (hNormal β) (hBR β)
    ell tau Delta hell htau.le hDelta (hReserve β) (hBRb β) (hLb β)
    (hInputb β) (hInputbarb β) (hCutb β) (hEtab β) (hNormalb β) (hDiff β)
  have hsAb := fun β k hk z hz => (hsA β k hk z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_left Ka Kd) htau.le)
  have hsBb := fun β k hk z hz => (hsB β k hk z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_left Ka Kd) htau.le)
  have hsDb := fun β k hk z hz => (hsD β k hk z hz).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right Ka Kd) htau.le) hDelta)
  have ha := parameterRound2_actual_globalCorrection_sum_split_scale F hF g input ν realChannel n length j Rsub horder
    W hW hsupport hinverse kappa Omega S U Sloc hOmega hSOmega hkappa hmapW hU hOU hSloc hsource hphi hmap
    hA hB hG hJ hT tau ell Mg Ks htau htaul hell1 hMg hKs hsrc T hTnonneg
    hAb hBb hGb hJb hTb hsAb hphib hRsub
  have hb := parameterRound2_actual_globalCorrection_sum_split_scale F hF g inputbar ν realChannel n length j Rsub horder
    W hW hsupport hinverse kappa Omega S U Sloc hOmega hSOmega hkappa hmapW hU hOU hSloc hsource hphi hmap
    hA hB hG hJ hT tau ell Mg Ks htau htaul hell1 hMg hKs hsrcbar T hTnonneg
    hAb hBb hGb hJb hTb hsBb hphib hRsub
  have hd := parameterRound2_actual_globalCorrection_difference_sum_split_scale F hF g input inputbar ν realChannel n length j Rsub horder
    W hW hsupport hinverse kappa Omega S U Sloc hOmega hSOmega hkappa hmapW hU hOU hSloc hsource hphi hmap
    hA hB hG hJ hT tau ell Mg Ks Delta htau htaul hell1 hMg hKs hDelta hsrc hsrcbar T hTnonneg
    hAb hBb hGb hJb hTb hsDb hphib hRsub
  let ch : (Fin (m+1) → ℂ) →L[ℝ] D := if realChannel then incrementsModeRealPart else incrementsModeImagPart
  have hch : ‖ch‖ ≤ Kch := by
    cases realChannel
    · exact le_add_of_nonneg_left (norm_nonneg _)
    · exact le_add_of_nonneg_right (norm_nonneg _)
  have hmajor : (Rsub:ℝ)*(actualFastChartTransferPrefix T j*
      (actualJointHomogeneousReconstructionCost m j Mg*‖ch‖*Ks*
        (∑ a ∈ Finset.range length, (2*2^n*Mg)^a))) ≤ K := by
    dsimp only [K]
    rw [mul_assoc (Rsub:ℝ)]
    gcongr
  refine ⟨⟨ha.1,hb.1⟩,?_,?_,?_⟩
  · intro k hk z hz
    exact (ha.2 k hk z hz).trans (mul_le_mul_of_nonneg_right hmajor (sq_nonneg tau))
  · intro k hk z hz
    exact (hb.2 k hk z hz).trans (mul_le_mul_of_nonneg_right hmajor (sq_nonneg tau))
  · intro k hk z hz
    exact (hd.2 k hk z hz).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmajor (sq_nonneg tau)) hDelta)

#print axioms parameterRound2_actual_primitive_globalCorrection_sum_uniform_split_scale_index
end GlobalEmbedding.Continuation
