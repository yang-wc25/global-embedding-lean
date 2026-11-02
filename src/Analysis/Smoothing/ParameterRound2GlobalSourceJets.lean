import Probes.ActualIncrementPrimaryOriginalFree
import Probes.ActualIncrementJointPrimaryError

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

theorem parameterRound2_actual_original_source_jets_uniform
    (n : ℕ) (c Bnd : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (ν : Λ) (β : Β) (S : Set X) (hSO : S ⊆ (g.chart ν β).target)
      (L : X → T →L[ℝ] ℝ) (A : X → T)
      (hL : ContDiffOn ℝ ∞ L (g.chart ν β).target)
      (hA : ContDiffOn ℝ ∞ A (g.chart ν β).target)
      (hRep : ∀ z ∈ (g.chart ν β).target,
        L z (A z) = g.linearArgument ν z.1 (g.inverse ν β z.1 z.2)
          (input z.1 (g.inverse ν β z.1 z.2)))
      (hCut : ContDiffOn ℝ ∞ (fun z : X => g.cutoff ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (hEta : ContDiffOn ℝ ∞ (fun z : X => g.eta ν β (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (hNormal : ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (hBR : ContDiffOn ℝ ∞ (fun z : X => fun a : Fin (m+1) =>
        (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 a : V)) (g.chart ν β).target)
      (ell tau : ℝ) (hell : 0 < ell) (htau : 0 ≤ tau)
      (hReserve : ∀ z ∈ S, c ≤ L z (A z))
      (hBRb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => fun a : Fin (m+1) =>
          (incrementsModeSecondForm (F w.1) (hF w.1) (g.inverse ν β w.1) w.2 0 a : V)) z‖ ≤ Bnd)
      (hLb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r L z‖ ≤ Bnd)
      (hAb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r A z‖ ≤ Bnd)
      (hCutb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.cutoff ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
      (hEtab : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.eta ν β (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
      (hNormalb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.normal ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd),
    ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (incrementsGlobalPrimarySource F hF g input tau ν β) z‖ ≤ K*tau := by
  obtain ⟨Kfree,hKfree,hFree⟩ := actual_original_primary_free_jets_uniform
    (I := I) (M := M) (Ep := Ep) (T := T) (m := m) (N := N) (Λ := Λ) (Β := Β) n c Bnd hc hBnd
  let Lsource := (2:ℝ) • incrementsModeComplexInclude (m := m)
  let Pair := incrementsModeForcingSourcePairing (m := m) (N := N)
  let Ksource := ‖Lsource‖*2^n*‖Pair‖*Bnd*Kfree
  refine ⟨Ksource,by dsimp only [Ksource]; positivity,?_⟩
  intro F hF g input ν β S hSO L A hL hA hRep hCut hEta hNormal hBR
    ell tau hell htau hReserve hBRb hLb hAb hCutb hEtab hNormalb
  let positive := (g.chart ν β).target ∩ {z | 0 < L z (A z)}
  have hPos : IsOpen positive :=
    (hL.clm_apply hA).continuousOn.isOpen_inter_preimage (g.chart ν β).open_target isOpen_Ioi
  have hPosO : positive ⊆ (g.chart ν β).target := fun z hz => hz.1
  have hSpos : S ⊆ positive := fun z hz => ⟨hSO hz,hc.trans_le (hReserve z hz)⟩
  let vf := fun z : X => (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1 z.2 : V)
  let Brow := fun z : X => fun a : Fin (m+1) =>
    (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 a : V)
  have hSqrt : ContDiffOn ℝ ∞ (fun z => Real.sqrt (L z (A z))) positive :=
    ((hL.clm_apply hA).mono hPosO).sqrt (fun z hz => hz.2.ne')
  have hvf : ContDiffOn ℝ ∞ vf positive := by
    apply (((hEta.mono hPosO).mul
      (((hCut.mono hPosO).mul hSqrt).const_smul (Real.sqrt 2*tau))).smul
        (hNormal.mono hPosO)).congr
    intro z hz
    change vf z = (g.eta ν β (z.1,g.inverse ν β z.1 z.2) *
      ((Real.sqrt 2*tau)*(g.cutoff ν (z.1,g.inverse ν β z.1 z.2)*Real.sqrt (L z (A z))))) •
        g.normal ν (z.1,g.inverse ν β z.1 z.2)
    simp only [vf,incrementsGlobalPrimaryLocalFree,dif_pos hz.1,Submodule.coe_smul,
      Submodule.coe_mk,incrementsGlobalPrimaryB,Pi.smul_apply,hRep z hz.1,smul_eq_mul]
  have hvfb := hFree F g input ν β S hSO L A hL hA hRep hCut hEta hNormal
    ell tau hell htau hReserve hLb hAb hCutb hEtab hNormalb
  have heq : incrementsGlobalPrimarySource F hF g input tau ν β =
      fun z => Lsource (Pair (Brow z) (vf z)) := by
    funext z
    have hzero : incrementsModeSource (F z.1) (hF z.1) (g.inverse ν β z.1)
        (fun _ _ _ => 0) (fun _ => 0) z.2 = 0 := by
      simpa only [zero_smul] using incrementsModeSource_zero_smul (F z.1) (hF z.1)
        (g.inverse ν β z.1) (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1) z.2 0
    unfold incrementsGlobalPrimarySource
    rw [incrementsModeSource_eq_zeroFree_add,hzero,zero_add,map_smul]
    rfl
  have hBrow : ContDiffOn ℝ ∞ Brow positive := hBR.mono hPosO
  have hprod : ContDiffOn ℝ ∞ (fun z => Pair (Brow z) (vf z)) positive :=
    (Pair.contDiff.comp_contDiffOn hBrow).clm_apply hvf
  intro r hr z hz
  rw [heq]
  have hp := slow_bilinear_jet_bound_norm Pair positive hPos Brow vf hBrow hvf r ell Bnd
    (Kfree*tau) hell.le z (hSpos hz)
    (fun i hi => hBRb i (hi.trans hr) z hz)
    (fun i hi => hvfb i (hi.trans hr) z hz)
  have hl := slow_linear_jet_bound Lsource positive hPos (fun z => Pair (Brow z) (vf z))
    hprod r ell (2^r*(‖Pair‖*Bnd)*(Kfree*tau)) hell.le z (hSpos hz) hp
  calc
    _ ≤ ‖Lsource‖*(2^r*(‖Pair‖*Bnd)*(Kfree*tau)) := hl
    _ ≤ ‖Lsource‖*(2^n*(‖Pair‖*Bnd)*(Kfree*tau)) := by gcongr; norm_num
    _ = Ksource*tau := by dsimp only [Ksource]; ring

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.parameterRound2_actual_original_source_jets_uniform
