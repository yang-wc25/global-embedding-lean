import GlobalEmbedding.Paper.IncrementsGlobalPrimaryMeanBinding
import Probes.ActualJointHomogeneousReconstruction
import Probes.ActualJointChartTransfer

/-!
# The SAME global primary correction in its actual subordinate chart

The real correction is the original fullZ extension minus eta times its
original free datum. It equals the actual finite homogeneous reconstruction
composed with that subordinate chart, with zero outside. The only support
input is the original relative support of eta*cutoff. No output cutoff or
independent correction is introduced; different subordinate charts remain
different throughout these identities.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

variable (F : Ep → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)

/-- The actual homogeneous reconstruction of the SAME original finite U. -/
def parameterRound2_globalLocalCorrection
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β) (z : X) : V :=
  let ch := if realChannel then incrementsModeRealPart else incrementsModeImagPart
  incrementsModeReconstruction (F z.1) (hF z.1) (g.inverse ν β z.1)
    (fun x => ch (incrementsGlobalPrimaryFiniteU F hF g input length tau ν β z.1 x)) z.2

/-- This is exactly the correction used in original GlobalObservedError. -/
def parameterRound2_globalCorrection
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β) (z : Ep × M) : V :=
  incrementsGlobalPrimaryExtension F hF g input length tau realChannel ν β z -
    if realChannel then g.eta ν β z • incrementsGlobalPrimaryFree F g input tau ν z else 0

theorem parameterRound2_globalLocalZ_split
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β) (z : X)
    (hz : z ∈ (g.chart ν β).target) :
    incrementsGlobalPrimaryLocalZ F hF g input length tau realChannel ν β z =
      parameterRound2_globalLocalCorrection F hF g input length tau realChannel ν β z +
        if realChannel then g.eta ν β (z.1,g.inverse ν β z.1 z.2) •
          incrementsGlobalPrimaryFree F g input tau ν (z.1,g.inverse ν β z.1 z.2) else 0 := by
  cases realChannel <;>
    simp [incrementsGlobalPrimaryLocalZ, parameterRound2_globalLocalCorrection,
      incrementsModeFullReconstruction, incrementsModeTransverseSource,
      incrementsGlobalPrimaryLocalFree, hz, incrementsGlobalPrimaryFree, smul_smul]
  all_goals exact map_zero _

/-- Inside the actual subordinate source, the original global correction is
the exact local finite reconstruction through that SAME chart. -/
theorem parameterRound2_globalCorrection_eq_on_source
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β)
    (hinverse : ∀ z ∈ (g.chart ν β).target,
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2))
    (z : Ep × M) (hz : z ∈ (g.chart ν β).source) :
    parameterRound2_globalCorrection F hF g input length tau realChannel ν β z =
      parameterRound2_globalLocalCorrection F hF g input length tau realChannel ν β (g.chart ν β z) := by
  have hid : ((g.chart ν β z).1,g.inverse ν β (g.chart ν β z).1 (g.chart ν β z).2) = z :=
    (hinverse _ ((g.chart ν β).map_source hz)).symm.trans ((g.chart ν β).left_inv hz)
  unfold parameterRound2_globalCorrection incrementsGlobalPrimaryExtension
  rw [if_pos hz, parameterRound2_globalLocalZ_split F hF g input length tau realChannel ν β _
    ((g.chart ν β).map_source hz),hid]
  exact add_sub_cancel_right _ _

theorem parameterRound2_global_eta_free_zero
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (tau : ℝ) (ν : Λ) (β : Β) (z : Ep × M)
    (hz : g.eta ν β z * g.cutoff ν z = 0) :
    g.eta ν β z • incrementsGlobalPrimaryFree F g input tau ν z = 0 := by
  have hs : g.eta ν β z *
      (Real.sqrt 2*tau*(g.cutoff ν z*Real.sqrt (g.linearArgument ν z.1 z.2 (input z.1 z.2)))) = 0 := by
    calc
      _ = (Real.sqrt 2*tau*Real.sqrt (g.linearArgument ν z.1 z.2 (input z.1 z.2))) *
          (g.eta ν β z*g.cutoff ν z) := by ring
      _ = 0 := by rw [hz,mul_zero]
  simpa only [incrementsGlobalPrimaryFree,incrementsGlobalPrimaryB,smul_smul,hs,zero_smul]

/-- Actual correction extension with the ORIGINAL primitive support supplier.
No output support or extension identity is hypothesized. -/
theorem parameterRound2_globalCorrection_eq_conditional
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β)
    (W : Set (Ep × M))
    (hsupport : incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ (g.chart ν β).source)
    (hinverse : ∀ z ∈ (g.chart ν β).target,
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2))
    (z : Ep × M) (hzW : z ∈ W) :
    parameterRound2_globalCorrection F hF g input length tau realChannel ν β z =
      if z ∈ (g.chart ν β).source then
        parameterRound2_globalLocalCorrection F hF g input length tau realChannel ν β (g.chart ν β z)
      else 0 := by
  classical
  by_cases hz : z ∈ (g.chart ν β).source
  · rw [if_pos hz]
    exact parameterRound2_globalCorrection_eq_on_source F hF g input length tau realChannel ν β hinverse z hz
  · have hzero : g.eta ν β z*g.cutoff ν z = 0 := by
      by_contra hn
      apply hz
      apply hsupport
      exact ⟨⟨z,hzW⟩,subset_tsupport (fun w : W => g.eta ν β w.val*g.cutoff ν w.val) hn,rfl⟩
    have hfzero := parameterRound2_global_eta_free_zero F g input tau ν β z hzero
    cases realChannel <;>
      simp [parameterRound2_globalCorrection,incrementsGlobalPrimaryExtension,hz,hfzero]

#print axioms parameterRound2_globalLocalZ_split
#print axioms parameterRound2_globalCorrection_eq_conditional
end GlobalEmbedding.Continuation
