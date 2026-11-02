import NormalPolar.ActualRepairModelFirstDefectAmplitude
import Smoothing.ParameterRound2PhysicalCoefficientIndex

/-! Regrouping the same subordinate amplitudes into the common unit-cutoff
array preserves their true physical derivative coefficient. This uses actual
finite-sum differentiability; no phase regularity is imposed outside support. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold Filter GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem actualRepairModelFirstDefect_unit_sum_coefficient
    {a N : ℕ} {Sub : Type*} [Fintype Sub]
    (phi : EuclideanSpace ℝ (Fin a) → ℝ) (tau : ℝ)
    (P Q : Sub → EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin a))
    (hP : ∀ b, DifferentiableAt ℝ (P b) x) (hQ : ∀ b, DifferentiableAt ℝ (Q b) x) :
    incrementsPrimaryDerivativeCoefficient phi tau (fun (_ : Unit) _ => 1)
      (fun _ y => ∑ b, P b y) (fun _ y => ∑ b, Q b y) x v =
    incrementsPrimaryDerivativeCoefficient phi tau (fun (_ : Sub) _ => 1) P Q x v := by
  funext co
  have hp : DifferentiableAt ℝ (fun y => ∑ b, P b y) x := DifferentiableAt.fun_sum (fun b _ => hP b)
  have hq : DifferentiableAt ℝ (fun y => ∑ b, Q b y) x := DifferentiableAt.fun_sum (fun b _ => hQ b)
  have hu := increments_primary_correction_coefficient_eq phi tau
    (fun (_ : Unit) y => ∑ b, P b y) (fun (_ : Unit) y => ∑ b, Q b y) x v co
    (fun _ => hp) (fun _ => hq)
  have hs := increments_primary_correction_coefficient_eq phi tau P Q x v co hP hQ
  have he : incrementsPrimaryCorrectionSum (fun (_ : Unit) y => ∑ b, P b y)
      (fun (_ : Unit) y => ∑ b, Q b y) co = incrementsPrimaryCorrectionSum P Q co := by
    funext y
    simp only [incrementsPrimaryCorrectionSum,Finset.univ_unique,Finset.sum_singleton,
      map_sum,Finset.smul_sum,Finset.sum_add_distrib]
  rw [he] at hu
  exact hu.trans hs.symm

variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem actualRepairModelFirstDefect_background_unit_coefficients_from_raw_uniform
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ MD : ℝ, 0 ≤ MD ∧ ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β]
      (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (W : Set (Ep × M)) (K : Λ → Set (Ep × M))
      (e : OpenPartialHomeomorph M D)
      (he : ContMDiffOn I 𝓘(ℝ,D) ∞ e e.source)
      (heInv : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
      (Omega S : Set X) (tau ell Delta : ℝ)
      (raw : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n (q+2) j Rsub Lprimary
        reserve Bnd Mg T F hF g input inputbar W K e Omega S tau ell Delta)
      (hTarget : ∀ z ∈ Omega, z.2 ∈ e.target) (delta : ℝ) (l : Λ),
    let coeff := fun z : X => incrementsSecondaryPhysicalCoefficient
      (fun l b x => g.phase l (b,e.symm x)) tau (fun (_ : Λ) (_ : Ep) (_ : Unit) _ => 1)
      (fun l b (_ : Unit) x => delta • incrementsGlobalPrimaryAmplitude F hF g input (q+2) tau true l (b,e.symm x))
      (fun l b (_ : Unit) x => delta • incrementsGlobalPrimaryAmplitude F hF g input (q+2) tau false l (b,e.symm x))
      (fun i _ => EuclideanSpace.single i 1) z l
    ContDiffOn ℝ ∞ coeff Omega ∧
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k coeff z‖ ≤ MD*|delta|) ∧
      (∀ z ∈ Omega, (z.1,e.symm z.2) ∉ K l → coeff =ᶠ[𝓝 z] 0) := by
  obtain ⟨MD,hMD,hraw⟩ := parameterRound2_original_physical_coefficient_profiles_from_raw_index
    (I := I) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N)
    n q j Rsub Lprimary hq horder reserve Bnd Mg hreserve hBnd hMg T hT
  refine ⟨MD,hMD,?_⟩
  intro Λ Β _ _ F hF g input inputbar W K e he heInv Omega S tau ell Delta raw hTarget delta l coeff
  let h := raw.prim
  have hreg := actual_global_primary_extension_regular F hF g input (q+2) tau W h.hW K h.hPrimary
    h.hPrimarySupport h.hSourceW h.hChart h.hChartInv h.hInverse h.hCombinedSupport h.hCut h.hNormal
    h.hArgument h.hEta h.hPositive h.hG h.hJ h.hT0 h.hA h.hB h.hSecond
  have hobs : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod I) ∞
      (fun z : X => (z.1,e.symm z.2)) Omega := by
    have hf : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ (fun z : X => z.1) Omega := contDiffOn_fst.contMDiffOn
    have hs : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,D) ∞ (fun z : X => z.2) Omega := contDiffOn_snd.contMDiffOn
    exact hf.prodMk (heInv.comp hs (fun z hz => hTarget z hz))
  have hext (ch : Bool) (b : Β) : ContDiffOn ℝ ∞
      (fun z : X => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau ch l b (z.1,e.symm z.2)) Omega := by
    have hh : ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞
        (incrementsGlobalPrimaryExtension F hF g input (q+2) tau ch l b) W := by
      cases ch with
      | false => exact (hreg l b).2.2.2.1
      | true => exact (hreg l b).2.2.1
    exact ((hh.comp hobs raw.hmapWO).contDiffOn).const_smul delta
  let subcoeff := fun z : X => incrementsSecondaryPhysicalCoefficient
    (fun l b x => g.phase l (b,e.symm x)) tau (fun _ _ (_ : Β) _ => 1)
    (fun l b beta x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau true l beta (b,e.symm x))
    (fun l b beta x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau false l beta (b,e.symm x))
    (fun i _ => EuclideanSpace.single i 1) z l
  have heq : EqOn coeff subcoeff Omega := by
    intro z hz
    funext i
    have hd (ch : Bool) (b : Β) : DifferentiableAt ℝ
        (fun x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau ch l b (z.1,e.symm x)) z.2 := by
      exact (((hext ch b).contDiffAt (raw.hO.mem_nhds hz)).comp z.2
        (contDiff_const.prodMk contDiff_id).contDiffAt).differentiableAt (by simp)
    simpa only [coeff,subcoeff,incrementsSecondaryPhysicalCoefficient,incrementsGlobalPrimaryAmplitude,Finset.smul_sum]
      using actualRepairModelFirstDefect_unit_sum_coefficient
        (fun x => g.phase l (z.1,e.symm x)) tau
        (fun b x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau true l b (z.1,e.symm x))
        (fun b x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau false l b (z.1,e.symm x))
        z.2 (EuclideanSpace.single i 1) (hd true) (hd false)
  obtain ⟨hs,hb,hz⟩ := hraw F hF g input inputbar W K e he heInv Omega S tau ell Delta raw hTarget delta l
  have hg (z : X) (hz : z ∈ Omega) : coeff =ᶠ[𝓝 z] subcoeff :=
    eventuallyEq_of_mem (raw.hO.mem_nhds hz) (fun y hy => heq hy)
  refine ⟨hs.congr heq,?_,?_⟩
  · intro k hk z hzS
    rw [((hg z (raw.hSO hzS)).iteratedFDeriv ℝ k).eq_of_nhds]
    exact hb k hk z hzS
  · intro z hzO hn
    exact (hg z hzO).trans (hz z hzO (fun hcut => hn (h.hPrimarySupport l hcut)))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_background_unit_coefficients_from_raw_uniform
