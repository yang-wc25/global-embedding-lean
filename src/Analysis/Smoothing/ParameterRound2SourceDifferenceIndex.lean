import Smoothing.ParameterRound2GlobalSourceDifference
import Smoothing.ParameterRound2SourceJetsIndex

/-! The SAME original global primary source is produced from its genuine
conditional LocalFree and actual second-form row. All source jets are derived
from primitive L/input/cutoff/eta/normal and geometry profiles; no free/source
or correction budget is assumed. Full joint derivatives retain one tau. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D


theorem parameterRound2_actual_original_source_difference_jets_uniform_index
    (n : ℕ) (c Bnd : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β] (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (ν : Λ) (β : Β) (S : Set X) (hSO : S ⊆ (g.chart ν β).target)
      (L : X → T →L[ℝ] ℝ) (A Abar : X → T)
      (hL : ContDiffOn ℝ ∞ L (g.chart ν β).target)
      (hA : ContDiffOn ℝ ∞ A (g.chart ν β).target)
      (hAbar : ContDiffOn ℝ ∞ Abar (g.chart ν β).target)
      (hRep : ∀ z ∈ (g.chart ν β).target,
        L z (A z) = g.linearArgument ν z.1 (g.inverse ν β z.1 z.2)
          (input z.1 (g.inverse ν β z.1 z.2)))
      (hRepbar : ∀ z ∈ (g.chart ν β).target,
        L z (Abar z) = g.linearArgument ν z.1 (g.inverse ν β z.1 z.2)
          (inputbar z.1 (g.inverse ν β z.1 z.2)))
      (hCut : ContDiffOn ℝ ∞ (fun z : X => g.cutoff ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (hEta : ContDiffOn ℝ ∞ (fun z : X => g.eta ν β (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (hNormal : ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (hBR : ContDiffOn ℝ ∞ (fun z : X => fun a : Fin (m+1) =>
        (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 a : V)) (g.chart ν β).target)
      (ell tau Delta : ℝ) (hell : 0 < ell) (htau : 0 ≤ tau) (hDelta : 0 ≤ Delta)
      (hReserve : ∀ z ∈ S, c ≤ L z (A z) ∧ c ≤ L z (Abar z))
      (hBRb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => fun a : Fin (m+1) =>
          (incrementsModeSecondForm (F w.1) (hF w.1) (g.inverse ν β w.1) w.2 0 a : V)) z‖ ≤ Bnd)
      (hLb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r L z‖ ≤ Bnd)
      (hAb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r A z‖ ≤ Bnd)
      (hAbarb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r Abar z‖ ≤ Bnd)
      (hCutb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.cutoff ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
      (hEtab : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.eta ν β (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
      (hNormalb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.normal ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
      (hDiff : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r (fun w => A w-Abar w) z‖ ≤ Delta),
    ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w => incrementsGlobalPrimarySource F hF g input tau ν β w -
        incrementsGlobalPrimarySource F hF g inputbar tau ν β w) z‖ ≤ K*tau*Delta := by
  obtain ⟨Kfree,hKfree,hFree⟩ := parameterRound2_original_primary_free_difference_jets_uniform_index
    (I := I) (M := M) (Ep := Ep) (T := T) (m := m) (N := N) n c Bnd hc hBnd
  let Lsource := (2:ℝ) • incrementsModeComplexInclude (m := m)
  let Pair := incrementsModeForcingSourcePairing (m := m) (N := N)
  let Ksource := ‖Lsource‖*2^n*‖Pair‖*Bnd*Kfree
  refine ⟨Ksource,by dsimp only [Ksource]; positivity,?_⟩
  intro Λ Β _ _ F hF g input inputbar ν β S hSO L A Abar hL hA hAbar hRep hRepbar hCut hEta hNormal hBR
    ell tau Delta hell htau hDelta hReserve hBRb hLb hAb hAbarb hCutb hEtab hNormalb hDiff
  let positive := (g.chart ν β).target ∩ {z | 0 < L z (A z)} ∩ {z | 0 < L z (Abar z)}
  have hPos : IsOpen positive := by
    have ha : IsOpen ((g.chart ν β).target ∩ {z | 0 < L z (A z)}) :=
      (hL.clm_apply hA).continuousOn.isOpen_inter_preimage
      (g.chart ν β).open_target isOpen_Ioi
    have hb : IsOpen ((g.chart ν β).target ∩ {z | 0 < L z (Abar z)}) :=
      (hL.clm_apply hAbar).continuousOn.isOpen_inter_preimage
      (g.chart ν β).open_target isOpen_Ioi
    convert ha.inter hb using 1
    ext z
    simp only [positive,Set.mem_inter_iff,Set.mem_ofPred_eq]
    tauto
  have hPosO : positive ⊆ (g.chart ν β).target := fun z hz => hz.1.1
  have hSpos : S ⊆ positive := fun z hz =>
    ⟨⟨hSO hz,hc.trans_le (hReserve z hz).1⟩,hc.trans_le (hReserve z hz).2⟩
  let vf := fun z : X => (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1 z.2 : V)
  let vfbar := fun z : X => (incrementsGlobalPrimaryLocalFree F g inputbar tau ν β z.1 z.2 : V)
  let Brow := fun z : X => fun a : Fin (m+1) =>
    (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 a : V)
  have hSqrt : ContDiffOn ℝ ∞ (fun z => Real.sqrt (L z (A z))) positive :=
    ((hL.clm_apply hA).mono hPosO).sqrt (fun z hz => hz.1.2.ne')
  have hSqrtbar : ContDiffOn ℝ ∞ (fun z => Real.sqrt (L z (Abar z))) positive :=
    ((hL.clm_apply hAbar).mono hPosO).sqrt (fun z hz => hz.2.ne')
  have hvf : ContDiffOn ℝ ∞ vf positive := by
    apply (((hEta.mono hPosO).mul
      (((hCut.mono hPosO).mul hSqrt).const_smul (Real.sqrt 2*tau))).smul
        (hNormal.mono hPosO)).congr
    intro z hz
    change vf z = (g.eta ν β (z.1,g.inverse ν β z.1 z.2) *
      ((Real.sqrt 2*tau)*(g.cutoff ν (z.1,g.inverse ν β z.1 z.2)*Real.sqrt (L z (A z))))) •
        g.normal ν (z.1,g.inverse ν β z.1 z.2)
    simp only [vf,incrementsGlobalPrimaryLocalFree,dif_pos hz.1.1,Submodule.coe_smul,
      Submodule.coe_mk,incrementsGlobalPrimaryB,hRep z hz.1.1]
  have hvfbar : ContDiffOn ℝ ∞ vfbar positive := by
    apply (((hEta.mono hPosO).mul
      (((hCut.mono hPosO).mul hSqrtbar).const_smul (Real.sqrt 2*tau))).smul
        (hNormal.mono hPosO)).congr
    intro z hz
    change vfbar z = (g.eta ν β (z.1,g.inverse ν β z.1 z.2) *
      ((Real.sqrt 2*tau)*(g.cutoff ν (z.1,g.inverse ν β z.1 z.2)*Real.sqrt (L z (Abar z))))) •
        g.normal ν (z.1,g.inverse ν β z.1 z.2)
    simp only [vfbar,incrementsGlobalPrimaryLocalFree,dif_pos hz.1.1,Submodule.coe_smul,
      Submodule.coe_mk,incrementsGlobalPrimaryB,hRepbar z hz.1.1]
  have hvfb := hFree F g input inputbar ν β S hSO L A Abar hL hA hAbar hRep hRepbar
    hCut hEta hNormal ell tau Delta hell htau hDelta hReserve hLb hAb hAbarb
    hCutb hEtab hNormalb hDiff
  have heq : (fun w => incrementsGlobalPrimarySource F hF g input tau ν β w -
      incrementsGlobalPrimarySource F hF g inputbar tau ν β w) =
      fun z => Lsource (Pair (Brow z) (vf z-vfbar z)) := by
    funext z
    rw [parameterRound2_actual_original_source_eq_pairing,
      parameterRound2_actual_original_source_eq_pairing]
    exact (map_sub Lsource _ _).symm.trans (congrArg Lsource ((map_sub (Pair (Brow z)) _ _).symm))
  have hBrow : ContDiffOn ℝ ∞ Brow positive := hBR.mono hPosO
  have hprod : ContDiffOn ℝ ∞ (fun z => Pair (Brow z) (vf z-vfbar z)) positive :=
    (Pair.contDiff.comp_contDiffOn hBrow).clm_apply (hvf.sub hvfbar)
  intro r hr z hz
  rw [heq]
  have hp := slow_bilinear_jet_bound_norm Pair positive hPos Brow (fun z => vf z-vfbar z)
    hBrow (hvf.sub hvfbar) r ell Bnd (Kfree*tau*Delta) hell.le z (hSpos hz)
    (fun i hi => hBRb i (hi.trans hr) z hz)
    (fun i hi => hvfb i (hi.trans hr) z hz)
  have hl := slow_linear_jet_bound Lsource positive hPos (fun z => Pair (Brow z) (vf z-vfbar z))
    hprod r ell (2^r*(‖Pair‖*Bnd)*(Kfree*tau*Delta)) hell.le z (hSpos hz) hp
  calc
    _ ≤ ‖Lsource‖*(2^r*(‖Pair‖*Bnd)*(Kfree*tau*Delta)) := hl
    _ ≤ ‖Lsource‖*(2^n*(‖Pair‖*Bnd)*(Kfree*tau*Delta)) := by gcongr; norm_num
    _ = Ksource*tau*Delta := by dsimp only [Ksource]; ring

#print axioms parameterRound2_actual_original_source_eq_pairing
#print axioms parameterRound2_actual_original_source_difference_jets_uniform_index
end GlobalEmbedding.Continuation
