import Smoothing.ParameterRound2SplitGlobalPrimitiveCorrectionSum
import Smoothing.ParameterRound2ObserverFree
import Smoothing.ParameterRound2GlobalObservedDifference

/-! Actual global observed error from raw input profiles in every OWN
subordinate chart and the actual observer. All sources, homogeneous
reconstructions, support sums, free jets and error jets are produced.
No source, R, Free, Error or mean budget occurs among the hypotheses.
Only the already-derived qualitative source smoothness remains an input.
-/

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

theorem parameterRound2_actual_primitive_globalObservedError_bounds_uniform_split_scale
    (n length j Rsub : ℕ) (r : Fin (m+1)) (coord : Fin N) (horder : j+2+length ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hTnonneg : ∀ i, 0 ≤ T i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (ν : Λ)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hsupport : ∀ β, incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ (g.chart ν β).source)
    (hinverse : ∀ β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2))
    (e : OpenPartialHomeomorph M D) (Omega S : Set X) (U : Β → Set X) (Sloc : Β → Set X)
    (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn (fun z : X => (z.1,e.symm z.2)) Omega) (hmapW : MapsTo (fun z : X => (z.1,e.symm z.2)) Omega W)
    (hU : ∀ β, IsOpen (U β))
    (hOU : ∀ β, Omega ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ U β)
    (hSloc : ∀ β, Sloc β ⊆ (g.chart ν β).target)
    (hsource : ∀ β, MapsTo (fun z : X => (z.1,e.symm z.2)) (U β) (g.chart ν β).source)
    (hphi : ∀ β, ContDiffOn ℝ ∞ (fun z => g.chart ν β ((fun z : X => (z.1,e.symm z.2)) z)) (U β))
    (hmap : ∀ β, MapsTo (fun z => g.chart ν β ((fun z : X => (z.1,e.symm z.2)) z))
      (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (fun z => g.eta ν β z*g.cutoff ν z)) (Sloc β))
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
    (hGb : ∀ β k, k ≤ j+1 → ∀ z ∈ Sloc β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ β k, k ≤ j+1 → ∀ z ∈ Sloc β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (g.inverse ν β w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ β k, k ≤ j+1 → ∀ z ∈ Sloc β, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hphib : ∀ β i, 1 ≤ i → i ≤ j+1 → ∀ z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (fun w => g.eta ν β w*g.cutoff ν w),
      ell^(i-1) * ‖iteratedFDeriv ℝ i (fun w => g.chart ν β ((fun z : X => (z.1,e.symm z.2)) w)) z‖ ≤ T i)
    (hRsub : ∀ z ∈ S, (Finset.univ.filter (fun β => (fun z : X => (z.1,e.symm z.2)) z ∈
      incrementsGlobalRelativeSupport W (fun w => g.eta ν β w*g.cutoff ν w))).card ≤ Rsub)
    (Lobs : X → Tr →L[ℝ] ℝ) (Aobs Abarobs : X → Tr)
    (hLobs : ContDiffOn ℝ ∞ Lobs Omega)
    (hAobs : ContDiffOn ℝ ∞ Aobs Omega) (hAbarobs : ContDiffOn ℝ ∞ Abarobs Omega)
    (hRepobs : ∀ z ∈ Omega, Lobs z (Aobs z) =
      g.linearArgument ν z.1 (e.symm z.2) (input z.1 (e.symm z.2)))
    (hRepbarobs : ∀ z ∈ Omega, Lobs z (Abarobs z) =
      g.linearArgument ν z.1 (e.symm z.2) (inputbar z.1 (e.symm z.2)))
    (hCutobs : ContDiffOn ℝ ∞ (fun z : X => g.cutoff ν (z.1,e.symm z.2)) Omega)
    (hNormalobs : ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,e.symm z.2)) Omega)
    (hPhaseobs : ContDiffOn ℝ ∞ (fun z : X => g.phase ν (z.1,e.symm z.2)) Omega)
    (hReserveobs : ∀ z ∈ S, c ≤ Lobs z (Aobs z) ∧ c ≤ Lobs z (Abarobs z))
    (hLobsb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k Lobs z‖ ≤ Bnd)
    (hAobsb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k Aobs z‖ ≤ Bnd)
    (hAbarobsb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k Abarobs z‖ ≤ Bnd)
    (hCutobsb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => g.cutoff ν (w.1,e.symm w.2)) z‖ ≤ Bnd)
    (hNormalobsb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => g.normal ν (w.1,e.symm w.2)) z‖ ≤ Bnd)
    (hGradobsb : ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => fderiv ℝ (fun x => g.phase ν (w.1,e.symm x)) w.2 (EuclideanSpace.single r 1)) z‖ ≤ Bnd)
    (hDiffobs : ∀ k ≤ j+1, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun w => Aobs w-Abarobs w) z‖ ≤ Delta),
    let positive := Omega ∩ {z | 0 < Lobs z (Aobs z)} ∩ {z | 0 < Lobs z (Abarobs z)}
    let errA := fun z : X => incrementsGlobalObservedError F hF g input length tau e z.1 z.2 ν r coord
    let errB := fun z : X => incrementsGlobalObservedError F hF g inputbar length tau e z.1 z.2 ν r coord
    (ContDiffOn ℝ ∞ errA positive ∧ ContDiffOn ℝ ∞ errB positive) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k errA z‖ ≤ K*(tau/ell)) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k errB z‖ ≤ K*(tau/ell)) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => errA w-errB w) z‖ ≤ K*(tau/ell)*Delta) := by
  obtain ⟨Kr,hKr,hRsum⟩ := parameterRound2_actual_primitive_globalCorrection_sum_uniform_split_scale
    (I := I) (M := M) (Ep := Ep) (Y := X) (Tr := Tr) (m := m) (N := N) (Λ := Λ) (Β := Β)
    n length (j+1) Rsub (by omega) c Bnd Mg hc hBnd hMg T hTnonneg
  obtain ⟨Cv,hCv,hFree⟩ := parameterRound2_actual_observer_free_bounds_uniform
    (I := I) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (Λ := Λ) (Β := Β)
    (j+1) c Bnd hc hBnd
  let Cz := actualJointCorrectionSumCost N 1 coord Kr Kr
  have hCz : 0 ≤ Cz := actualJointCorrectionSumCost_nonneg 1 coord hKr hKr
  let K := actualJointPrimaryErrorCost j (EuclideanSpace.single r 1) coord Cv Cz Bnd
  refine ⟨K,actualJointPrimaryErrorCost_nonneg j _ coord hCv hCz hBnd,?_⟩
  intro F hF g input inputbar ν W hW hsupport hinverse e Omega S U Sloc
    hOmega hSOmega hkappa hmapW hU hOU hSloc hsource hphi hmap hA hB hG hJ hT
    tau ell Delta htau htaul hell1 hDelta hsrc hsrcbar
    L A Abar hL hInput hInputbar hRep hRepbar hCut hEta hNormal hBR hReserve
    hBRb hLb hInputb hInputbarb hCutb hEtab hNormalb hDiff
    hAb hBb hGb hJb hTb hphib hRsub
    Lobs Aobs Abarobs hLobs hAobs hAbarobs hRepobs hRepbarobs hCutobs hNormalobs hPhaseobs
    hReserveobs hLobsb hAobsb hAbarobsb hCutobsb hNormalobsb hGradobsb hDiffobs positive errA errB
  let kappa := fun z : X => (z.1,e.symm z.2)
  have hell : 0 < ell := htau.trans_le htaul
  have hR (ch : Bool) := hRsum F hF g input inputbar ν ch W hW hsupport hinverse kappa Omega S U Sloc
    hOmega hSOmega hkappa hmapW hU hOU hSloc hsource hphi hmap hA hB hG hJ hT
    tau ell Delta htau htaul hell1 hDelta hsrc hsrcbar
    L A Abar hL hInput hInputbar hRep hRepbar hCut hEta hNormal hBR hReserve
    hBRb hLb hInputb hInputbarb hCutb hEtab hNormalb hDiff
    hAb hBb hGb hJb hTb hphib hRsub
  have hFrees := hFree F g input inputbar ν e Omega S hOmega hSOmega Lobs Aobs Abarobs
    hLobs hAobs hAbarobs hRepobs hRepbarobs hCutobs hNormalobs ell tau Delta hell htau.le hDelta
    hReserveobs hLobsb hAobsb hAbarobsb hCutobsb hNormalobsb hDiffobs
  have hPos : IsOpen positive := by
    have ha : IsOpen (Omega ∩ {z | 0 < Lobs z (Aobs z)}) :=
      (hLobs.clm_apply hAobs).continuousOn.isOpen_inter_preimage hOmega isOpen_Ioi
    have hb : IsOpen (Omega ∩ {z | 0 < Lobs z (Abarobs z)}) :=
      (hLobs.clm_apply hAbarobs).continuousOn.isOpen_inter_preimage hOmega isOpen_Ioi
    convert ha.inter hb using 1
    ext z
    simp only [positive,Set.mem_inter_iff,Set.mem_ofPred_eq]
    tauto
  have hPosO : positive ⊆ Omega := fun z hz => hz.1.1
  have hSpos : S ⊆ positive := fun z hz =>
    ⟨⟨hSOmega hz,hc.trans_le (hReserveobs z hz).1⟩,hc.trans_le (hReserveobs z hz).2⟩
  have hregA (ch : Bool) (β : Β) : ContDiffOn ℝ ∞
      (fun z : X => parameterRound2_globalCorrection F hF g input length tau ch ν β (kappa z)) positive :=
    (parameterRound2_globalCorrection_observation_contDiffOn F hF g input length tau ch ν β W hW
      (hsupport β) (hinverse β) kappa Omega (U β) hOmega hkappa hmapW (hU β) (hOU β)
      (hsource β) (hphi β) (hA β) (hB β) (hG β) (hJ β) (hT β) (hsrc β)).mono hPosO
  have hregB (ch : Bool) (β : Β) : ContDiffOn ℝ ∞
      (fun z : X => parameterRound2_globalCorrection F hF g inputbar length tau ch ν β (kappa z)) positive :=
    (parameterRound2_globalCorrection_observation_contDiffOn F hF g inputbar length tau ch ν β W hW
      (hsupport β) (hinverse β) kappa Omega (U β) hOmega hkappa hmapW (hU β) (hOU β)
      (hsource β) (hphi β) (hA β) (hB β) (hG β) (hJ β) (hT β) (hsrcbar β)).mono hPosO
  have hEA := parameterRound2_actual_globalObservedError_slow_jets F hF g input length j ν e r coord
    positive S hPos hSpos tau ell Cv Kr Kr Bnd hell htau htaul hCv hKr hKr hBnd
    hFrees.1.1 (hNormalobs.mono hPosO) (hPhaseobs.mono hPosO) (hregA true) (hregA false)
    hFrees.2.2.1 (hR true).2.1 (hR false).2.1 hGradobsb
  have hEB := parameterRound2_actual_globalObservedError_slow_jets F hF g inputbar length j ν e r coord
    positive S hPos hSpos tau ell Cv Kr Kr Bnd hell htau htaul hCv hKr hKr hBnd
    hFrees.1.2 (hNormalobs.mono hPosO) (hPhaseobs.mono hPosO) (hregB true) (hregB false)
    hFrees.2.2.2.1 (hR true).2.2.1 (hR false).2.2.1 hGradobsb
  have hED := parameterRound2_actual_globalObservedError_difference_slow_jets F hF g input inputbar length j ν e r coord
    positive S hPos hSpos tau ell Cv Kr Kr Bnd Delta hell htau htaul hDelta hCv hKr hKr hBnd
    hFrees.1.1 hFrees.1.2 (hNormalobs.mono hPosO) (hPhaseobs.mono hPosO)
    (hregA true) (hregA false) (hregB true) (hregB false)
    hFrees.2.2.2.2 (hR true).2.2.2 (hR false).2.2.2 hGradobsb
  exact ⟨⟨hEA.1,hEB.1⟩,hEA.2,hEB.2,hED.2⟩

#print axioms parameterRound2_actual_primitive_globalObservedError_bounds_uniform_split_scale
end GlobalEmbedding.Continuation
