import Smoothing.ParameterRound2SplitObservedErrorIndex
import Smoothing.ParameterRound2ObserverLeadingIndex
import Smoothing.ParameterRound2MeanTensorAlgebra

/-! Complete raw-input producer of the SAME global leading/error coefficient
arrays. Different subordinate charts and every parameter derivative remain
in the actual constructions. The fixed direction/ambient coordinate sums
choose one constant before F/g/input; there is no total label/chart count.
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

theorem parameterRound2_actual_primitive_globalCoefficient_profiles_uniform_split_scale_index
    (n length j Rsub : ℕ) (horder : j+2+length ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hTnonneg : ∀ i, 0 ≤ T i) :
    ∃ Mcoef : ℝ, 0 ≤ Mcoef ∧ ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β]
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) F)
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
    (hGradobsb : ∀ r : Fin (m+1), ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => fderiv ℝ (fun x => g.phase ν (w.1,e.symm x)) w.2 (EuclideanSpace.single r 1)) z‖ ≤ Bnd)
    (hDiffobs : ∀ k ≤ j+1, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun w => Aobs w-Abarobs w) z‖ ≤ Delta),
    let positive := Omega ∩ {z | 0 < Lobs z (Aobs z)} ∩ {z | 0 < Lobs z (Abarobs z)}
    let LA := fun z : X => incrementsGlobalObservedLeading F g input e z.1 z.2 ν
    let LB := fun z : X => incrementsGlobalObservedLeading F g inputbar e z.1 z.2 ν
    let EA := fun z : X => incrementsGlobalObservedError F hF g input length tau e z.1 z.2 ν
    let EB := fun z : X => incrementsGlobalObservedError F hF g inputbar length tau e z.1 z.2 ν
    (ContDiffOn ℝ ∞ LA positive ∧ ContDiffOn ℝ ∞ LB positive) ∧
    (ContDiffOn ℝ ∞ EA positive ∧ ContDiffOn ℝ ∞ EB positive) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k LA z‖ ≤ Mcoef) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k LB z‖ ≤ Mcoef) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k EA z‖ ≤ Mcoef*(tau/ell)) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k EB z‖ ≤ Mcoef*(tau/ell)) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => LA w-LB w) z‖ ≤ Mcoef*Delta) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => EA w-EB w) z‖ ≤ Mcoef*(tau/ell)*Delta) := by
  choose Ce hCe hError using (fun (r : Fin (m+1)) (co : Fin N) =>
    parameterRound2_actual_primitive_globalObservedError_bounds_uniform_split_scale_index
      (I := I) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N)
      n length j Rsub r co horder c Bnd Mg hc hBnd hMg T hTnonneg)
  choose Cl hCl hLeading using (fun (r : Fin (m+1)) (co : Fin N) =>
    parameterRound2_actual_observer_leading_bounds_uniform_index
      (I := I) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N)
      j r co c Bnd hc hBnd)
  let Mcoef := ∑ a : Fin (m+1) × Fin N, (Ce a.1 a.2+Cl a.1 a.2)
  have hMcoef : 0 ≤ Mcoef := Finset.sum_nonneg (fun a _ => add_nonneg (hCe a.1 a.2) (hCl a.1 a.2))
  have hCeM (r) (co) : Ce r co ≤ Mcoef := (le_add_of_nonneg_right (hCl r co)).trans
    (Finset.single_le_sum (fun a _ => add_nonneg (hCe a.1 a.2) (hCl a.1 a.2)) (Finset.mem_univ (r,co)))
  have hClM (r) (co) : Cl r co ≤ Mcoef := (le_add_of_nonneg_left (hCe r co)).trans
    (Finset.single_le_sum (fun a _ => add_nonneg (hCe a.1 a.2) (hCl a.1 a.2)) (Finset.mem_univ (r,co)))
  refine ⟨Mcoef,hMcoef,?_⟩
  intro Λ Β _ _ F hF g input inputbar ν W hW hsupport hinverse e Omega S U Sloc
    hOmega hSOmega hkappa hmapW hU hOU hSloc hsource hphi hmap hA hB hG hJ hT
    tau ell Delta htau htaul hell1 hDelta hsrc hsrcbar
    L A Abar hL hInput hInputbar hRep hRepbar hCut hEta hNormal hBR hReserve
    hBRb hLb hInputb hInputbarb hCutb hEtab hNormalb hDiff
    hAb hBb hGb hJb hTb hphib hRsub
    Lobs Aobs Abarobs hLobs hAobs hAbarobs hRepobs hRepbarobs hCutobs hNormalobs hPhaseobs
    hReserveobs hLobsb hAobsb hAbarobsb hCutobsb hNormalobsb hGradobsb hDiffobs positive LA LB EA EB
  have hell : 0 < ell := htau.trans_le htaul
  have hE (r) (co) := hError r co F hF g input inputbar ν W hW hsupport hinverse e Omega S U Sloc
    hOmega hSOmega hkappa hmapW hU hOU hSloc hsource hphi hmap hA hB hG hJ hT
    tau ell Delta htau htaul hell1 hDelta hsrc hsrcbar
    L A Abar hL hInput hInputbar hRep hRepbar hCut hEta hNormal hBR hReserve
    hBRb hLb hInputb hInputbarb hCutb hEtab hNormalb hDiff
    hAb hBb hGb hJb hTb hphib hRsub
    Lobs Aobs Abarobs hLobs hAobs hAbarobs hRepobs hRepbarobs hCutobs hNormalobs hPhaseobs
    hReserveobs hLobsb hAobsb hAbarobsb hCutobsb hNormalobsb (hGradobsb r) hDiffobs
  have hL (r) (co) := hLeading r co F g input inputbar ν e Omega S hOmega hSOmega
    Lobs Aobs Abarobs hLobs hAobs hAbarobs hRepobs hRepbarobs hCutobs hNormalobs hPhaseobs
    ell Delta hell hDelta hReserveobs
    (fun k hk => hLobsb k (by omega)) (fun k hk => hAobsb k (by omega))
    (fun k hk => hAbarobsb k (by omega)) (fun k hk => hCutobsb k (by omega))
    (fun k hk => hNormalobsb k (by omega)) (hGradobsb r) (fun k hk => hDiffobs k (by omega))
  have hPos : IsOpen positive := by
    have ha : IsOpen (Omega ∩ {z | 0 < Lobs z (Aobs z)}) :=
      (hLobs.clm_apply hAobs).continuousOn.isOpen_inter_preimage hOmega isOpen_Ioi
    have hb : IsOpen (Omega ∩ {z | 0 < Lobs z (Abarobs z)}) :=
      (hLobs.clm_apply hAbarobs).continuousOn.isOpen_inter_preimage hOmega isOpen_Ioi
    convert ha.inter hb using 1
    ext z
    simp only [positive,Set.mem_inter_iff,Set.mem_ofPred_eq]
    tauto
  have hSpos : S ⊆ positive := fun z hz =>
    ⟨⟨hSOmega hz,hc.trans_le (hReserveobs z hz).1⟩,hc.trans_le (hReserveobs z hz).2⟩
  have hLA : ContDiffOn ℝ ∞ LA positive :=
    contDiffOn_pi.2 (fun r => contDiffOn_pi.2 (fun co => (hL r co).1.1))
  have hLB : ContDiffOn ℝ ∞ LB positive :=
    contDiffOn_pi.2 (fun r => contDiffOn_pi.2 (fun co => (hL r co).1.2))
  have hEA : ContDiffOn ℝ ∞ EA positive :=
    contDiffOn_pi.2 (fun r => contDiffOn_pi.2 (fun co => (hE r co).1.1))
  have hEB : ContDiffOn ℝ ∞ EB positive :=
    contDiffOn_pi.2 (fun r => contDiffOn_pi.2 (fun co => (hE r co).1.2))
  have assemble (f : X → Fin (m+1) → Fin N → ℂ) (hf : ContDiffOn ℝ ∞ f positive)
      (R : ℝ) (hR : 0 ≤ R)
      (hb : ∀ r co, ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => f w r co) z‖ ≤ R) :
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k f z‖ ≤ R := by
    intro k hk z hz
    have hfz := hf.contDiffAt (hPos.mem_nhds (hSpos hz))
    apply parameterRound2_joint_pi_weighted_jet f z hfz k ell R hell hR
    intro r
    apply parameterRound2_joint_pi_weighted_jet (fun w => f w r) z (contDiffAt_pi.1 hfz r) k ell R hell hR
    intro co
    exact hb r co k hk z hz
  have heps : 0 ≤ tau/ell := by positivity
  refine ⟨⟨hLA,hLB⟩,⟨hEA,hEB⟩,?_,?_,?_,?_,?_,?_⟩
  · exact assemble LA hLA Mcoef hMcoef (fun r co k hk z hz => ((hL r co).2.1 k hk z hz).trans (hClM r co))
  · exact assemble LB hLB Mcoef hMcoef (fun r co k hk z hz => ((hL r co).2.2.1 k hk z hz).trans (hClM r co))
  · exact assemble EA hEA (Mcoef*(tau/ell)) (mul_nonneg hMcoef heps)
      (fun r co k hk z hz => ((hE r co).2.1 k hk z hz).trans (mul_le_mul_of_nonneg_right (hCeM r co) heps))
  · exact assemble EB hEB (Mcoef*(tau/ell)) (mul_nonneg hMcoef heps)
      (fun r co k hk z hz => ((hE r co).2.2.1 k hk z hz).trans (mul_le_mul_of_nonneg_right (hCeM r co) heps))
  · exact assemble (fun w => LA w-LB w) (hLA.sub hLB) (Mcoef*Delta) (mul_nonneg hMcoef hDelta)
      (fun r co k hk z hz => ((hL r co).2.2.2 k hk z hz).trans (mul_le_mul_of_nonneg_right (hClM r co) hDelta))
  · exact assemble (fun w => EA w-EB w) (hEA.sub hEB) (Mcoef*(tau/ell)*Delta)
      (mul_nonneg (mul_nonneg hMcoef heps) hDelta)
      (fun r co k hk z hz => ((hE r co).2.2.2 k hk z hz).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCeM r co) heps) hDelta))

#print axioms parameterRound2_actual_primitive_globalCoefficient_profiles_uniform_split_scale_index
end GlobalEmbedding.Continuation
