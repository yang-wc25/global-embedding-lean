import Smoothing.ParameterRound2SplitPrimitiveGlobalCoefficients
import Smoothing.ParameterRound2GlobalMeanJets

/-! The literal ALL-primary global mean remainder from primitive data.
Each primary uses its own active observer open, each beta its own actual
adapted chart. Inactive zero germs and the genuine primary local count are
proved consumers, not supplied output budgets. The same-input difference
retains one tau/ell factor and all joint parameter/source derivatives. -/

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

theorem parameterRound2_actual_primitive_globalMean_bounds_uniform_split_scale
    (n length j Rsub Lprimary : ℕ) (i i' : Fin (m+1)) (horder : j+2+length ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hTnonneg : ∀ i, 0 ≤ T i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀
    (F : Ep → M → V)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M))
    (hW : IsOpen W)
    (hsupport : ∀ ν, ∀ β, incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ (g.chart ν β).source)
    (hinverse : ∀ ν, ∀ β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2))
    (e : OpenPartialHomeomorph M D)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hkappaO : ContinuousOn (fun z : X => (z.1,e.symm z.2)) O)
    (hmapWO : MapsTo (fun z : X => (z.1,e.symm z.2)) O W)
    (Omega : Λ → Set X)
    (U : Λ → Β → Set X)
    (Sloc : Λ → Β → Set X)
    (hOmega : ∀ ν, IsOpen (Omega ν))
    (hSOmega : ∀ ν, (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)) ⊆ (Omega ν))
    (hkappa : ∀ ν, ContinuousOn (fun z : X => (z.1,e.symm z.2)) (Omega ν))
    (hmapW : ∀ ν, MapsTo (fun z : X => (z.1,e.symm z.2)) (Omega ν) W)
    (hU : ∀ ν, ∀ β, IsOpen (U ν β))
    (hOU : ∀ ν, ∀ β, (Omega ν) ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ U ν β)
    (hSloc : ∀ ν, ∀ β, Sloc ν β ⊆ (g.chart ν β).target)
    (hsource : ∀ ν, ∀ β, MapsTo (fun z : X => (z.1,e.symm z.2)) (U ν β) (g.chart ν β).source)
    (hphi : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (fun z => g.chart ν β ((fun z : X => (z.1,e.symm z.2)) z)) (U ν β))
    (hmap : ∀ ν, ∀ β, MapsTo (fun z => g.chart ν β ((fun z : X => (z.1,e.symm z.2)) z))
      ((S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)) ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (fun z => g.eta ν β z*g.cutoff ν z)) (Sloc ν β))
    (hA : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hB : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hG : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hJ : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hT : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (tau ell Delta : ℝ)
    (htau : 0 < tau)
    (htaul : tau ≤ ell)
    (hell1 : ell ≤ 1)
    (hDelta : 0 ≤ Delta)
    (hsrc : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g input tau ν β) (g.chart ν β).target)
    (hsrcbar : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g inputbar tau ν β) (g.chart ν β).target)
    (L : Λ → Β → X → Tr →L[ℝ] ℝ)
    (A Abar : Λ → Β → X → Tr)
    (hL : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (L ν β) (g.chart ν β).target)
    (hInput : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (A ν β) (g.chart ν β).target)
    (hInputbar : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (Abar ν β) (g.chart ν β).target)
    (hRep : ∀ ν, ∀ β z, z ∈ (g.chart ν β).target → L ν β z (A ν β z) =
      g.linearArgument ν z.1 (g.inverse ν β z.1 z.2) (input z.1 (g.inverse ν β z.1 z.2)))
    (hRepbar : ∀ ν, ∀ β z, z ∈ (g.chart ν β).target → L ν β z (Abar ν β z) =
      g.linearArgument ν z.1 (g.inverse ν β z.1 z.2) (inputbar z.1 (g.inverse ν β z.1 z.2)))
    (hCut : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (fun z : X => g.cutoff ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
    (hEta : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (fun z : X => g.eta ν β (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
    (hNormal : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
    (hBR : ∀ ν, ∀ β, ContDiffOn ℝ ∞ (fun z : X => fun a : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 a : V)) (g.chart ν β).target)
    (hReserve : ∀ ν, ∀ β z, z ∈ Sloc ν β → c ≤ L ν β z (A ν β z) ∧ c ≤ L ν β z (Abar ν β z))
    (hBRb : ∀ ν, ∀ β r, r ≤ n → ∀ z ∈ Sloc ν β, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => fun a : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (g.inverse ν β w.1) w.2 0 a : V)) z‖ ≤ Bnd)
    (hLb : ∀ ν, ∀ β r, r ≤ n → ∀ z ∈ Sloc ν β, ell^r * ‖iteratedFDeriv ℝ r (L ν β) z‖ ≤ Bnd)
    (hInputb : ∀ ν, ∀ β r, r ≤ n → ∀ z ∈ Sloc ν β, ell^r * ‖iteratedFDeriv ℝ r (A ν β) z‖ ≤ Bnd)
    (hInputbarb : ∀ ν, ∀ β r, r ≤ n → ∀ z ∈ Sloc ν β, ell^r * ‖iteratedFDeriv ℝ r (Abar ν β) z‖ ≤ Bnd)
    (hCutb : ∀ ν, ∀ β r, r ≤ n → ∀ z ∈ Sloc ν β, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => g.cutoff ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
    (hEtab : ∀ ν, ∀ β r, r ≤ n → ∀ z ∈ Sloc ν β, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => g.eta ν β (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
    (hNormalb : ∀ ν, ∀ β r, r ≤ n → ∀ z ∈ Sloc ν β, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => g.normal ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
    (hDiff : ∀ ν, ∀ β r, r ≤ n → ∀ z ∈ Sloc ν β, ell^r * ‖iteratedFDeriv ℝ r
      (fun w => A ν β w-Abar ν β w) z‖ ≤ Delta)
    (hAb : ∀ ν, ∀ β k, k ≤ n → ∀ z ∈ Sloc ν β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ ν, ∀ β k, k ≤ n → ∀ z ∈ Sloc ν β, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hGb : ∀ ν, ∀ β k, k ≤ j+1 → ∀ z ∈ Sloc ν β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ ν, ∀ β k, k ≤ j+1 → ∀ z ∈ Sloc ν β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (g.inverse ν β w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ ν, ∀ β k, k ≤ j+1 → ∀ z ∈ Sloc ν β, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hphib : ∀ ν, ∀ β i, 1 ≤ i → i ≤ j+1 → ∀ z ∈ (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)) ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (fun w => g.eta ν β w*g.cutoff ν w),
      ell^(i-1) * ‖iteratedFDeriv ℝ i (fun w => g.chart ν β ((fun z : X => (z.1,e.symm z.2)) w)) z‖ ≤ T i)
    (hRsub : ∀ ν, ∀ z ∈ (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)), (Finset.univ.filter (fun β => (fun z : X => (z.1,e.symm z.2)) z ∈
      incrementsGlobalRelativeSupport W (fun w => g.eta ν β w*g.cutoff ν w))).card ≤ Rsub)
    (Lobs : Λ → X → Tr →L[ℝ] ℝ)
    (Aobs Abarobs : Λ → X → Tr)
    (hLobs : ∀ ν, ContDiffOn ℝ ∞ (Lobs ν) (Omega ν))
    (hAobs : ∀ ν, ContDiffOn ℝ ∞ (Aobs ν) (Omega ν))
    (hAbarobs : ∀ ν, ContDiffOn ℝ ∞ (Abarobs ν) (Omega ν))
    (hRepobs : ∀ ν, ∀ z ∈ (Omega ν), (Lobs ν) z ((Aobs ν) z) =
      g.linearArgument ν z.1 (e.symm z.2) (input z.1 (e.symm z.2)))
    (hRepbarobs : ∀ ν, ∀ z ∈ (Omega ν), (Lobs ν) z ((Abarobs ν) z) =
      g.linearArgument ν z.1 (e.symm z.2) (inputbar z.1 (e.symm z.2)))
    (hCutobs : ∀ ν, ContDiffOn ℝ ∞ (fun z : X => g.cutoff ν (z.1,e.symm z.2)) (Omega ν))
    (hNormalobs : ∀ ν, ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,e.symm z.2)) (Omega ν))
    (hPhaseobs : ∀ ν, ContDiffOn ℝ ∞ (fun z : X => g.phase ν (z.1,e.symm z.2)) (Omega ν))
    (hReserveobs : ∀ ν, ∀ z ∈ (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)), c ≤ (Lobs ν) z ((Aobs ν) z) ∧ c ≤ (Lobs ν) z ((Abarobs ν) z))
    (hLobsb : ∀ ν, ∀ k ≤ j+1, ∀ z ∈ (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)), ell^k*‖iteratedFDeriv ℝ k (Lobs ν) z‖ ≤ Bnd)
    (hAobsb : ∀ ν, ∀ k ≤ j+1, ∀ z ∈ (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)), ell^k*‖iteratedFDeriv ℝ k (Aobs ν) z‖ ≤ Bnd)
    (hAbarobsb : ∀ ν, ∀ k ≤ j+1, ∀ z ∈ (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)), ell^k*‖iteratedFDeriv ℝ k (Abarobs ν) z‖ ≤ Bnd)
    (hCutobsb : ∀ ν, ∀ k ≤ j+1, ∀ z ∈ (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)), ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => g.cutoff ν (w.1,e.symm w.2)) z‖ ≤ Bnd)
    (hNormalobsb : ∀ ν, ∀ k ≤ j+1, ∀ z ∈ (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)), ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => g.normal ν (w.1,e.symm w.2)) z‖ ≤ Bnd)
    (hGradobsb : ∀ ν, ∀ r : Fin (m+1), ∀ k ≤ j, ∀ z ∈ (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)), ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => fderiv ℝ (fun x => g.phase ν (w.1,e.symm x)) w.2 (EuclideanSpace.single r 1)) z‖ ≤ Bnd)
    (hDiffobs : ∀ ν, ∀ k ≤ j+1, ∀ z ∈ (S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)), ell^k*‖iteratedFDeriv ℝ k
      (fun w => (Aobs ν) w-(Abarobs ν) w) z‖ ≤ Delta)
    (hCover : ∀ ν, O ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff ν) ⊆ Omega ν)
    (hPositiveCover : ∀ ν z, z ∈ O ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff ν) →
      0 < Lobs ν z (Aobs ν z) ∧ 0 < Lobs ν z (Abarobs ν z))
    (hCount : ∀ z ∈ S, (Finset.univ.filter (fun ν => (z.1,e.symm z.2) ∈
      incrementsGlobalRelativeSupport W (g.cutoff ν))).card ≤ Lprimary),
    let meanA := fun z => parameterRound2_globalObservedMeanCoefficient F hF g input length tau e z i i'
    let meanB := fun z => parameterRound2_globalObservedMeanCoefficient F hF g inputbar length tau e z i i'
    (ContDiffOn ℝ ∞ meanA O ∧ ContDiffOn ℝ ∞ meanB O) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k meanA z‖ ≤ K*(tau/ell)) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k meanB z‖ ≤ K*(tau/ell)) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => meanA w-meanB w) z‖ ≤ K*(tau/ell)*Delta) := by
  obtain ⟨Mcoef,hMcoef,hProfiles⟩ := parameterRound2_actual_primitive_globalCoefficient_profiles_uniform_split_scale
    (I := I) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (Λ := Λ) (Β := Β)
    n length j Rsub horder c Bnd Mg hc hBnd hMg T hTnonneg
  let K := (Lprimary:ℝ)*(6*‖incrementsMeanBilinear (Λ := Unit) (N := N) i i'‖*2^j*Mcoef^2)
  refine ⟨K,by dsimp only [K]; positivity,?_⟩
  intro F hF g input inputbar W hW hsupport hinverse e O S hO hSO hkappaO hmapWO Omega U Sloc hOmega hSOmega hkappa hmapW hU hOU hSloc hsource hphi hmap hA hB hG hJ hT tau ell Delta htau htaul hell1 hDelta hsrc hsrcbar L A Abar hL hInput hInputbar hRep hRepbar hCut hEta hNormal hBR hReserve hBRb hLb hInputb hInputbarb hCutb hEtab hNormalb hDiff hAb hBb hGb hJb hTb hphib hRsub Lobs Aobs Abarobs hLobs hAobs hAbarobs hRepobs hRepbarobs hCutobs hNormalobs hPhaseobs hReserveobs hLobsb hAobsb hAbarobsb hCutobsb hNormalobsb hGradobsb hDiffobs hCover hPositiveCover hCount meanA meanB
  let kappa := fun z : X => (z.1,e.symm z.2)
  let Sample := fun ν => S ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν)
  let positive := fun ν => Omega ν ∩ {z | 0 < Lobs ν z (Aobs ν z)} ∩ {z | 0 < Lobs ν z (Abarobs ν z)}
  have hP (ν) := hProfiles F hF g input inputbar ν W hW (hsupport ν) (hinverse ν) e
    (Omega ν) (Sample ν) (U ν) (Sloc ν) (hOmega ν) (hSOmega ν) (hkappa ν) (hmapW ν)
    (hU ν) (hOU ν) (hSloc ν) (hsource ν) (hphi ν) (hmap ν) (hA ν) (hB ν) (hG ν) (hJ ν) (hT ν)
    tau ell Delta htau htaul hell1 hDelta (hsrc ν) (hsrcbar ν)
    (L ν) (A ν) (Abar ν) (hL ν) (hInput ν) (hInputbar ν) (hRep ν) (hRepbar ν)
    (hCut ν) (hEta ν) (hNormal ν) (hBR ν) (hReserve ν) (hBRb ν) (hLb ν)
    (hInputb ν) (hInputbarb ν) (hCutb ν) (hEtab ν) (hNormalb ν) (hDiff ν)
    (hAb ν) (hBb ν) (hGb ν) (hJb ν) (hTb ν) (hphib ν) (hRsub ν)
    (Lobs ν) (Aobs ν) (Abarobs ν) (hLobs ν) (hAobs ν) (hAbarobs ν) (hRepobs ν) (hRepbarobs ν)
    (hCutobs ν) (hNormalobs ν) (hPhaseobs ν) (hReserveobs ν)
    (hLobsb ν) (hAobsb ν) (hAbarobsb ν) (hCutobsb ν) (hNormalobsb ν) (hGradobsb ν) (hDiffobs ν)
  have hPos (ν) : IsOpen (positive ν) := by
    have ha : IsOpen (Omega ν ∩ {z | 0 < Lobs ν z (Aobs ν z)}) :=
      ((hLobs ν).clm_apply (hAobs ν)).continuousOn.isOpen_inter_preimage (hOmega ν) isOpen_Ioi
    have hb : IsOpen (Omega ν ∩ {z | 0 < Lobs ν z (Abarobs ν z)}) :=
      ((hLobs ν).clm_apply (hAbarobs ν)).continuousOn.isOpen_inter_preimage (hOmega ν) isOpen_Ioi
    convert ha.inter hb using 1
    ext z
    simp only [positive,Set.mem_inter_iff,Set.mem_ofPred_eq]
    tauto
  have hPosCover (ν) : O ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff ν) ⊆ positive ν := by
    intro z hz
    exact ⟨⟨hCover ν hz,(hPositiveCover ν z hz).1⟩,(hPositiveCover ν z hz).2⟩
  have hout := parameterRound2_actual_globalMean_coefficient_jets F hF g input inputbar length j Lprimary i i'
    W hW hsupport hinverse e O S positive hO hSO hkappaO hmapWO hPos hPosCover hCount
    ell tau Mcoef Delta (htau.trans_le htaul) htau htaul hMcoef hDelta
    (fun ν => (hP ν).1.1) (fun ν => (hP ν).1.2) (fun ν => (hP ν).2.1.1) (fun ν => (hP ν).2.1.2)
    (fun ν => (hP ν).2.2.1) (fun ν => (hP ν).2.2.2.1)
    (fun ν => (hP ν).2.2.2.2.1) (fun ν => (hP ν).2.2.2.2.2.1)
    (fun ν => (hP ν).2.2.2.2.2.2.1) (fun ν => (hP ν).2.2.2.2.2.2.2)
  exact hout

#print axioms parameterRound2_actual_primitive_globalMean_bounds_uniform_split_scale
end GlobalEmbedding.Continuation
