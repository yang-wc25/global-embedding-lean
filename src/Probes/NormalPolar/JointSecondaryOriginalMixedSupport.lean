import NormalPolar.JointSecondaryOriginalMixedWaveFamily
import NormalPolar.JointSecondaryOriginalCarrierBinding

/-! On the original zero-dimensional reference parameter, the relative
cutoff slice is exactly the spatial topological support. This proved whole
carrier-function identity permits the same manufactured mixed seed family
to enter the original Atlas factory without selecting any geometry again. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade
open Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N r : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
variable (Data : IncrementsOriginalNativeData (m+1) d N M P)
  (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
  (p : P) (hpO : p ∈ Data.parameterOpen)
  (waves : Fin r → LocalLegalWave (n := m+1) (fun x => Data.F (p,x))
    (incrementsOriginal_slice_contMDiff Data hd hs p hpO))

variable [Subsingleton P]

include hd hpO in

theorem jointSecondaryOriginalPrimaryCarrier_eq_slice_tsupport (l : Fin Data.primaryCount) :
    jointSecondaryOriginalPrimaryCarrier Data p l = tsupport (fun x : M => Data.cutoff l (p,x)) := by
  apply Subset.antisymm
  · intro x hx
    have hts : (p,x) ∈ tsupport (Data.cutoff l) := by
      change (p,x) ∈ incrementsOriginalRelativeCutoffSupport Data l at hx
      rw [parameterRound2_original_relativeSupport_eq Data hd.parameter_open] at hx
      exact hx.2
    have heq : Data.cutoff l = (fun z : P × M => Data.cutoff l (p,z.2)) := by
      funext z
      exact congrArg (Data.cutoff l) (Prod.ext (Subsingleton.elim z.1 p) rfl)
    rw [heq] at hts
    exact tsupport_comp_subset_preimage (fun x : M => Data.cutoff l (p,x))
      (continuous_snd : Continuous (Prod.snd : P × M → M)) hts
  · exact jointSecondary_original_primary_slice_support Data hd p hpO l

theorem jointSecondaryOriginalMixedCarrier_eq_slice_tsupports :
    jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves =
      Sum.elim (fun l => tsupport (fun x : M => Data.cutoff l (p,x)))
        (fun l => tsupport ((waves l).cutoff : M → ℝ)) := by
  funext l
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryCarrier_eq_slice_tsupport Data hd p hpO l
  | inr l => rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondaryOriginalPrimaryCarrier_eq_slice_tsupport
#print axioms GlobalEmbedding.Continuation.jointSecondaryOriginalMixedCarrier_eq_slice_tsupports
