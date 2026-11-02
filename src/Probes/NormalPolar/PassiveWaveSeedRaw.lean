import NormalPolar.PassiveWaveSeedChart
import NormalPolar.PassiveParameterJets

/-! The full actual primitive raw geometry of a one-point seed lifts to
every normed parameter model. All fields are the original fields composed
with the actual projection, and every derivative budget is unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M S Ep : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [Subsingleton S]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The genuine seed raw coefficients and their exact same budgets on the
new full parameter model. Neither a solved amplitude nor an output norm is
an input to this construction. -/
def passiveWaveSeed_raw
    (F : S → M → V) (hF : ∀ s, ContMDiff I 𝓘(ℝ,V) ∞ (F s))
    (c : S → D → M) (chi : S × D → ℝ)
    (nu : (s : S) → (x : D) → normalSpace (I := I) (F s) (c s x))
    (a : OpenPartialHomeomorph (S × M) (S × D)) (W K : Set (S × M))
    (n j : ℕ) (ell Mg Bchi Bnu : ℝ)
    (raw : ActualPrescribedSpatialRawProfiles F hF c chi nu a W K n j ell Mg Bchi Bnu) :
    ActualPrescribedSpatialRawProfiles
      (fun _ : Ep => F 0) (fun _ => hF 0) (fun _ => c 0)
      (fun z : Ep × D => chi (0,z.2)) (fun _ => nu 0)
      (passiveParameterChart 0 a)
      ((fun z : Ep × M => (0,z.2)) ⁻¹' W)
      ((fun z : Ep × M => (0,z.2)) ⁻¹' K) n j ell Mg Bchi Bnu := by
  let L : (Ep × D) →L[ℝ] (S × D) := passiveParameterProjection
  refine {
    sample := L ⁻¹' raw.sample
    sample_subset := fun _ hz => raw.sample_subset hz
    closed_support := ?_
    support_source := fun _ hz => raw.support_source hz
    chart_smooth := passiveWaveSeed_chart_smooth 0 a raw.chart_smooth
    cutoff_support := ?_
    A_smooth := raw.A_smooth.comp_continuousLinearMap L
    B_smooth := raw.B_smooth.comp_continuousLinearMap L
    G_smooth := raw.G_smooth.comp_continuousLinearMap L
    J_smooth := raw.J_smooth.comp_continuousLinearMap L
    T_smooth := raw.T_smooth.comp_continuousLinearMap L
    BR_smooth := raw.BR_smooth.comp_continuousLinearMap L
    cutoff_smooth := raw.cutoff_smooth.comp_continuousLinearMap L
    normal_smooth := raw.normal_smooth.comp_continuousLinearMap L
    A_jets := ?_
    B_jets := ?_
    G_jets := ?_
    J_jets := ?_
    T_jets := ?_
    BR_jets := ?_
    cutoff_jets := ?_
    normal_jets := ?_ }
  · let κ : ((fun z : Ep × M => (0,z.2)) ⁻¹' W) → W :=
      fun z => ⟨(0,z.val.2),z.property⟩
    have hκ : Continuous κ :=
      (continuous_const.prodMk continuous_subtype_val.snd).subtype_mk _
    exact raw.closed_support.preimage hκ
  · intro z hz hchi
    have hs : (0,z.2) ∈ tsupport chi := tsupport_comp_subset_preimage chi L.continuous hchi
    have hK := raw.cutoff_support (0,z.2) hz hs
    have he : (0,(a.symm (0,z.2)).2) = a.symm (0,z.2) :=
      Prod.ext (Subsingleton.elim _ _) rfl
    change (0,(a.symm (0,z.2)).2) ∈ K
    rw [he]
    exact hK
  · intro k hk z hz
    rw [passiveParameter_iteratedFDeriv_norm (0 : S) _ a.target a.open_target
      raw.A_smooth z (raw.sample_subset hz) k (by simp)]
    exact raw.A_jets k hk (0,z.2) hz
  · intro k hk z hz
    rw [passiveParameter_iteratedFDeriv_norm (0 : S) _ a.target a.open_target
      raw.B_smooth z (raw.sample_subset hz) k (by simp)]
    exact raw.B_jets k hk (0,z.2) hz
  · intro k hk z hz
    rw [passiveParameter_iteratedFDeriv_norm (0 : S) _ a.target a.open_target
      raw.G_smooth z (raw.sample_subset hz) k (by simp)]
    exact raw.G_jets k hk (0,z.2) hz
  · intro k hk z hz
    rw [passiveParameter_iteratedFDeriv_norm (0 : S) _ a.target a.open_target
      raw.J_smooth z (raw.sample_subset hz) k (by simp)]
    exact raw.J_jets k hk (0,z.2) hz
  · intro k hk z hz
    rw [passiveParameter_iteratedFDeriv_norm (0 : S) _ a.target a.open_target
      raw.T_smooth z (raw.sample_subset hz) k (by simp)]
    exact raw.T_jets k hk (0,z.2) hz
  · intro k hk z hz
    rw [passiveParameter_iteratedFDeriv_norm (0 : S) _ a.target a.open_target
      raw.BR_smooth z hz k (by simp)]
    exact raw.BR_jets k hk (0,z.2) hz
  · intro k hk z hz
    rw [passiveParameter_iteratedFDeriv_norm (0 : S) _ a.target a.open_target
      raw.cutoff_smooth z hz k (by simp)]
    exact raw.cutoff_jets k hk (0,z.2) hz
  · intro k hk z hz
    rw [passiveParameter_iteratedFDeriv_norm (0 : S) _ a.target a.open_target
      raw.normal_smooth z hz k (by simp)]
    exact raw.normal_jets k hk (0,z.2) hz

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveWaveSeed_raw
