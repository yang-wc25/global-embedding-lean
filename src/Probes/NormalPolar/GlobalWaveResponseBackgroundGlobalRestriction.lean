import NormalPolar.GlobalWaveResponseBackgroundGlobal
import Smoothing.ParameterRound2PrimaryRestrictionMean

/-! The full original global background wave retains every two-point jet
bound supplied on pair-specific positive restrictions. No active-support
hypothesis is needed at the observer sample. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology
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

theorem globalWave_background_global_difference_at_fixed_sample
    (n length j Rsub Lprimary : ℕ) (horder : j+1+length ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β]
      (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I:=I) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
      (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (G : Set (Ep×M)) (hG : IsOpen G) (primary : Λ → Set (Ep×M))
      (e : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ)
      (raw : ParameterRound2GlobalMeanRawProfiles (Tr:=Tr) n length j Rsub Lprimary reserve Bnd Mg T
        F hF (parameterRound2_restrictPrimaryFamily F g G hG) input inputbar G primary e O S tau ell Delta)
      (hadapt : ∀ nu beta z, z ∈ (g.chart nu beta).source →
        g.phase nu z = (g.chart nu beta z).2 0),
    let A := fun y : X => incrementsGlobalPrimaryWave F hF g input length tau (y.1,e.symm y.2)
    let B := fun y : X => incrementsGlobalPrimaryWave F hF g inputbar length tau (y.1,e.symm y.2)
    ContDiffOn ℝ ∞ (fun y => A y-B y) O ∧
      ∀ k ≤ j, ∀ y ∈ S, tau^k*‖iteratedFDeriv ℝ k (fun z => A z-B z) y‖ ≤ C*tau*Delta := by
  obtain ⟨C,hC,hglobal⟩ := globalWave_background_global_raw_difference
    (I:=I) (M:=M) (Ep:=Ep) (Tr:=Tr) (m:=m) (N:=N) n length j Rsub Lprimary horder
      reserve Bnd Mg hc hBnd hMg T hT
  refine ⟨C,hC,?_⟩
  intro Λ Β _ _ F hF g input inputbar G hG primary e O S tau ell Delta raw hadapt A B
  let gG := parameterRound2_restrictPrimaryFamily F g G hG
  have ha : ∀ nu beta y, y ∈ raw.U nu beta →
      gG.phase nu (y.1,e.symm y.2) = (gG.chart nu beta (y.1,e.symm y.2)).2 0 := by
    intro nu beta y hy
    exact hadapt nu beta _ (raw.hsource nu beta hy).1
  have hh := hglobal F hF gG input inputbar G primary e O S tau ell Delta raw ha
  have heq : EqOn
      (fun y : X => incrementsGlobalPrimaryWave F hF gG input length tau (y.1,e.symm y.2)-
        incrementsGlobalPrimaryWave F hF gG inputbar length tau (y.1,e.symm y.2))
      (fun y => A y-B y) O := by
    intro y hy
    exact congrArg₂ Sub.sub
      (parameterRound2_restrictPrimary_wave F hF g G hG input length tau (raw.hmapWO hy))
      (parameterRound2_restrictPrimary_wave F hF g G hG inputbar length tau (raw.hmapWO hy))
  refine ⟨hh.1.congr heq.symm,?_⟩
  intro k hk y hy
  have hnear := heq.eventuallyEq_of_mem (raw.hO.mem_nhds (raw.hSO hy))
  rw [← (hnear.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hh.2 k hk y hy

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_background_global_difference_at_fixed_sample
