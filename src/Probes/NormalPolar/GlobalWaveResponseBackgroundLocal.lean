import NormalPolar.GlobalWaveResponseBackgroundFreeDifference
import Smoothing.ParameterRound2SourceDifferenceIndex
import Smoothing.ParameterRound2SplitCorrectionDifference
import Probes.ActualSecondaryModulation
import Probes.ActualSecondaryRemodulation

/-! Full local background waves, including the nonlinear free term and both
finite reconstructed channels, have primitive-raw two-point fast jet bounds.
The constants precede every field, parameter pair, scale, and sample. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep×D
local notation "Cdata" => Fin (m+1) → ℂ

/-- The full background finite formula, before its supported chart pullback. -/
def globalWaveBackgroundLocal {Λ Β : Type*} [Fintype Λ] [Fintype Β]
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I:=I) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (nu : Λ) (beta : Β) : X → V :=
  actualSecondaryModulation (fun z : X => z.2 0) tau
    (incrementsGlobalPrimaryLocalZ F hF g input length tau true nu beta)
    (incrementsGlobalPrimaryLocalZ F hF g input length tau false nu beta)

theorem globalWave_background_local_raw_difference
    (n length j : ℕ) (horder : j+1+length ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β]
      (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I:=I) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
      (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (W : Set (Ep×M)) (primary : Λ → Set (Ep×M))
      (e : OpenPartialHomeomorph M D) (O S : Set X)
      (Rsub Lprimary : ℕ) (T : ℕ → ℝ) (tau ell Delta : ℝ)
      (raw : ParameterRound2GlobalMeanRawProfiles (Tr:=Tr) n length j Rsub Lprimary reserve Bnd Mg T
        F hF g input inputbar W primary e O S tau ell Delta)
      (nu : Λ) (beta : Β),
    let A := globalWaveBackgroundLocal F hF g input length tau nu beta
    let B := globalWaveBackgroundLocal F hF g inputbar length tau nu beta
    ContDiffOn ℝ ∞ (fun z => A z-B z) (g.chart nu beta).target ∧
      ∀ k ≤ j, ∀ z ∈ raw.Sloc nu beta,
        tau^k*‖iteratedFDeriv ℝ k (fun w => A w-B w) z‖ ≤ C*tau*Delta := by
  obtain ⟨Kf,hKf,hfree⟩ := parameterRound2_original_primary_free_difference_jets_uniform_index
    (I:=I) (M:=M) (Ep:=Ep) (T:=Tr) (m:=m) (N:=N) n reserve Bnd hc hBnd
  obtain ⟨Ks,hKs,hsource⟩ := parameterRound2_actual_original_source_difference_jets_uniform_index
    (I:=I) (M:=M) (Ep:=Ep) (T:=Tr) (m:=m) (N:=N) n reserve Bnd hc hBnd
  let Cr := actualJointHomogeneousReconstructionCost m j Mg
  let Profile : ℝ := ∑ a ∈ Finset.range length, (2*2^n*Mg)^a
  let K := fun (ch : Cdata →L[ℝ] D) => Cr*‖ch‖*Ks*Profile
  have hCr : 0 ≤ Cr := actualJointHomogeneousReconstructionCost_nonneg m j hMg
  have hProf : 0 ≤ Profile := by dsimp only [Profile]; positivity
  have hK (ch : Cdata →L[ℝ] D) : 0 ≤ K ch := by dsimp only [K]; positivity
  let C := euclideanTargetCoordinateCost N * incrementsFastMultiplierConstant j 1 *
    (K incrementsModeRealPart+Kf+K incrementsModeImagPart)
  have hC : 0 ≤ C := by
    have hc' := euclideanTargetCoordinateCost_nonneg N
    have hp := (incrementsFastMultiplierConstant_pos j 1).le
    have hr := hK incrementsModeRealPart
    have hi := hK incrementsModeImagPart
    dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro Λ Β _ _ F hF g input inputbar W primary e O S Rsub Lprimary T tau ell Delta raw nu beta A B
  let Oloc := (g.chart nu beta).target
  have hOloc : IsOpen Oloc := (g.chart nu beta).open_target
  have hell : 0 < ell := raw.htau.trans_le raw.htaul
  have htau : 0 < tau := raw.htau
  have hDelta : 0 ≤ Delta := raw.hDelta
  have hreg (v : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (hp : ParameterRound2GlobalMeanPrimitives F hF g v W primary) :=
    actual_global_primary_extension_regular F hF g v length tau W hp.hW primary hp.hPrimary
      hp.hPrimarySupport hp.hSourceW hp.hChart hp.hChartInv hp.hInverse hp.hCombinedSupport
      hp.hCut hp.hNormal hp.hArgument hp.hEta hp.hPositive hp.hG hp.hJ hp.hT0 hp.hA hp.hB hp.hSecond
  let freeD := fun z : X =>
    (incrementsGlobalPrimaryLocalFree F g input tau nu beta z.1 z.2 : V)-
      (incrementsGlobalPrimaryLocalFree F g inputbar tau nu beta z.1 z.2 : V)
  have hfreeD : ContDiffOn ℝ ∞ freeD Oloc :=
    ((hreg input raw.prim nu beta).1).sub ((hreg inputbar raw.primbar nu beta).1)
  have hfreeb := hfree F g input inputbar nu beta (raw.Sloc nu beta) (raw.hSloc nu beta)
    (raw.L nu beta) (raw.A nu beta) (raw.Abar nu beta) (raw.hL nu beta) (raw.hInput nu beta)
    (raw.hInputbar nu beta) (raw.hRep nu beta) (raw.hRepbar nu beta) (raw.hCut nu beta)
    (raw.hEta nu beta) (raw.hNormal nu beta) ell tau Delta hell raw.htau.le raw.hDelta
    (raw.hReserve nu beta) (raw.hLb nu beta) (raw.hInputb nu beta) (raw.hInputbarb nu beta)
    (raw.hCutb nu beta) (raw.hEtab nu beta) (raw.hNormalb nu beta) (raw.hDiff nu beta)
  have hsourceb := hsource F hF g input inputbar nu beta (raw.Sloc nu beta) (raw.hSloc nu beta)
    (raw.L nu beta) (raw.A nu beta) (raw.Abar nu beta) (raw.hL nu beta) (raw.hInput nu beta)
    (raw.hInputbar nu beta) (raw.hRep nu beta) (raw.hRepbar nu beta) (raw.hCut nu beta)
    (raw.hEta nu beta) (raw.hNormal nu beta) (raw.hBR nu beta) ell tau Delta hell raw.htau.le raw.hDelta
    (raw.hReserve nu beta) (raw.hBRb nu beta) (raw.hLb nu beta) (raw.hInputb nu beta)
    (raw.hInputbarb nu beta) (raw.hCutb nu beta) (raw.hEtab nu beta) (raw.hNormalb nu beta) (raw.hDiff nu beta)
  let R := fun (v : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (ch : Cdata →L[ℝ] D) (z : X) =>
    incrementsPrimaryReconstructedChannel (F z.1) (hF z.1) (g.inverse nu beta z.1) ch tau length
      (fun x => incrementsGlobalPrimarySource F hF g v tau nu beta (z.1,x)) z.2
  let Rd := fun (ch : Cdata →L[ℝ] D) (z : X) => R input ch z-R inputbar ch z
  have hR (ch : Cdata →L[ℝ] D) : ContDiffOn ℝ ∞ (Rd ch) Oloc ∧
      ∀ k ≤ j, ∀ z ∈ raw.Sloc nu beta,
        ell^k*‖iteratedFDeriv ℝ k (Rd ch) z‖ ≤ K ch*tau*Delta := by
    have hKch := hK ch
    have hh := parameterRound2_actual_reconstructed_channel_difference_split_scale_jets F hF
      (g.inverse nu beta) (incrementsGlobalPrimarySource F hF g input tau nu beta)
      (incrementsGlobalPrimarySource F hF g inputbar tau nu beta) ch n length j horder Oloc
      (raw.Sloc nu beta) hOloc (raw.hSloc nu beta) (raw.prim.hA nu beta) (raw.prim.hB nu beta)
      (raw.prim.hG nu beta) (raw.prim.hJ nu beta) (raw.prim.hT0 nu beta)
      (hreg input raw.prim nu beta).2.1 (hreg inputbar raw.primbar nu beta).2.1
      tau ell Mg (Ks*tau*Delta) raw.htau raw.htaul raw.hell1 hMg (by positivity)
      (raw.hAb nu beta) (raw.hBb nu beta)
      (fun k hk => raw.hGb nu beta k (by omega)) (fun k hk => raw.hJb nu beta k (by omega))
      (fun k hk => raw.hTb nu beta k (by omega)) hsourceb
    refine ⟨hh.1,?_⟩
    intro k hk z hz
    have hb : ell^k*‖iteratedFDeriv ℝ k (Rd ch) z‖ ≤ K ch*tau*Delta*(tau/ell) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hell).mpr
      calc
        _ = ell^(k+1)*‖iteratedFDeriv ℝ k (Rd ch) z‖ := by rw [pow_succ]; ring
        _ ≤ _ := hh.2 k hk z hz
        _ = _ := by dsimp only [K,Cr,Profile]; ring
    exact hb.trans (mul_le_of_le_one_right (by positivity) ((div_le_one hell).mpr raw.htaul))
  have hZeq (v : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) (ch : Bool) :
      incrementsGlobalPrimaryLocalZ F hF g v length tau ch nu beta =
        fun z => R v (if ch then incrementsModeRealPart else incrementsModeImagPart) z+
          (if ch then (incrementsGlobalPrimaryLocalFree F g v tau nu beta z.1 z.2 : V) else 0) := by
    funext z
    have ht : incrementsModeTransverseSource (fun _ _ _ => (0 : ℝ)) z.2 = 0 := by
      ext q; simp [incrementsModeTransverseSource]
    cases ch <;>
      simp only [incrementsGlobalPrimaryLocalZ,Bool.false_eq_true,ite_false,ite_true,
        incrementsModeFullReconstruction,ht,map_zero,Submodule.coe_zero,smul_zero,sub_zero]
    · rfl
    · rfl
  let ZR := fun z => Rd incrementsModeRealPart z+freeD z
  let ZI := Rd incrementsModeImagPart
  have hZR : ContDiffOn ℝ ∞ ZR Oloc := (hR _).1.add hfreeD
  have hZI : ContDiffOn ℝ ∞ ZI Oloc := (hR _).1
  have heq : (fun z => A z-B z) = actualSecondaryModulation (fun z : X => z.2 0) tau ZR ZI := by
    funext z
    dsimp only [A,B,globalWaveBackgroundLocal,actualSecondaryModulation]
    rw [hZeq input true,hZeq input false,hZeq inputbar true,hZeq inputbar false]
    dsimp only [ZR,ZI,Rd,freeD]
    simp only [ite_true,Bool.false_eq_true,ite_false,add_zero,smul_add,smul_sub]
    abel
  have hp : ContDiffOn ℝ ∞ (fun z : X => z.2 0) Oloc :=
    (actualSecondaryCoordinatePhase (Ep:=Ep) (m:=m)).contDiff.contDiffOn
  have hpb : ∀ k < j, ∀ z ∈ raw.Sloc nu beta,
      ell^k*‖iteratedFDeriv ℝ (k+1) (fun w : X => w.2 0) z‖ ≤ 1 := by
    intro k _ z _
    exact actual_linear_phase_slow_jets (actualSecondaryCoordinatePhase (Ep:=Ep) (m:=m))
      (actualSecondaryCoordinatePhase_norm_le (Ep:=Ep) (m:=m)) ell z k
  have hZRb : ∀ k ≤ j, ∀ z ∈ raw.Sloc nu beta,
      ell^k*‖iteratedFDeriv ℝ k ZR z‖ ≤ (K incrementsModeRealPart+Kf)*tau*Delta := by
    intro k hk z hz
    exact (actual_joint_slow_add_jet_bound (Rd incrementsModeRealPart) freeD k ell _ _ hell.le z
      ((hR _).1.contDiffAt (hOloc.mem_nhds (raw.hSloc nu beta hz)) |>.of_le (by simp))
      (hfreeD.contDiffAt (hOloc.mem_nhds (raw.hSloc nu beta hz)) |>.of_le (by simp))
      ((hR _).2 k hk z hz) (hfreeb k (by omega) z hz)).trans_eq (by ring)
  rw [heq]
  refine ⟨actualSecondaryModulation_contDiffOn _ _ _ _ Oloc hp hZR hZI,?_⟩
  have hKR := hK incrementsModeRealPart
  have hKI := hK incrementsModeImagPart
  have hb := actualSecondaryModulation_weighted_jets j (fun z : X => z.2 0) ZR ZI Oloc
    (raw.Sloc nu beta) hOloc (raw.hSloc nu beta) hp hZR hZI tau ell 1
    ((K incrementsModeRealPart+Kf)*tau*Delta) (K incrementsModeImagPart*tau*Delta)
    raw.htau raw.htaul raw.hell1 (by positivity) (by positivity) hpb hZRb (hR _).2
  intro k hk z hz
  exact (hb k hk z hz).trans_eq (by dsimp only [C]; ring)

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_background_local_raw_difference
