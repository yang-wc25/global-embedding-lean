import NormalPolar.PassiveWaveSeedRaw
import NormalPolar.PassiveWaveSeedNativeChart

/-! Raw primitive profiles in the actual native chart of an arbitrary
physical parameter space. The parameter target is kept in the source,
target, carrier and sample; all spatial fields and budgets are unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M S P Ep : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [Subsingleton S]
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

def passiveWaveSeed_native_raw (B : OpenPartialHomeomorph P Ep)
    (F : S → M → V) (hF : ∀ s, ContMDiff I 𝓘(ℝ,V) ∞ (F s))
    (c : S → D → M) (chi : S × D → ℝ)
    (nu : (s : S) → (x : D) → normalSpace (I := I) (F s) (c s x))
    (a : OpenPartialHomeomorph (S × M) (S × D)) (W K : Set (S × M))
    (n j : ℕ) (ell Mg Bchi Bnu : ℝ)
    (raw : ActualPrescribedSpatialRawProfiles F hF c chi nu a W K n j ell Mg Bchi Bnu) :
    ActualPrescribedSpatialRawProfiles
      (fun _ : Ep => F 0) (fun _ => hF 0) (fun _ => c 0)
      (fun z : Ep × D => chi (0,z.2)) (fun _ => nu 0)
      (round3ParameterChartPullback B (passiveParameterChart 0 a))
      {z : Ep × M | z.1 ∈ B.target ∧ (0,z.2) ∈ W}
      {z : Ep × M | z.1 ∈ B.target ∧ (0,z.2) ∈ K} n j ell Mg Bchi Bnu := by
  let full := passiveWaveSeed_raw (Ep := Ep) F hF c chi nu a W K n j ell Mg Bchi Bnu raw
  let an := round3ParameterChartPullback B (passiveParameterChart (P := P) 0 a)
  have hs : an.source ⊆ (passiveParameterChart (P := Ep) 0 a).source :=
    fun z hz => ((passiveWaveSeed_native_source 0 B a z).mp hz).2
  have ht : an.target ⊆ (passiveParameterChart (P := Ep) 0 a).target :=
    fun z hz => ((passiveWaveSeed_native_target 0 B a z).mp hz).2
  refine {
    sample := {z : Ep × D | z.1 ∈ B.target ∧ (0,z.2) ∈ raw.sample}
    sample_subset := fun z hz => (passiveWaveSeed_native_target 0 B a z).mpr
      ⟨hz.1,raw.sample_subset hz.2⟩
    closed_support := ?_
    support_source := fun z hz => (passiveWaveSeed_native_source 0 B a z).mpr
      ⟨hz.1,raw.support_source hz.2⟩
    chart_smooth := (full.chart_smooth.mono hs).congr
      (fun z hz => passiveWaveSeed_native_apply 0 B a z
        ((passiveWaveSeed_native_source 0 B a z).mp hz).1)
    cutoff_support := ?_
    A_smooth := full.A_smooth.mono ht
    B_smooth := full.B_smooth.mono ht
    G_smooth := full.G_smooth.mono ht
    J_smooth := full.J_smooth.mono ht
    T_smooth := full.T_smooth.mono ht
    BR_smooth := full.BR_smooth.mono ht
    cutoff_smooth := full.cutoff_smooth.mono ht
    normal_smooth := full.normal_smooth.mono ht
    A_jets := fun k hk z hz => full.A_jets k hk z hz.2
    B_jets := fun k hk z hz => full.B_jets k hk z hz.2
    G_jets := fun k hk z hz => full.G_jets k hk z hz.2
    J_jets := fun k hk z hz => full.J_jets k hk z hz.2
    T_jets := fun k hk z hz => full.T_jets k hk z hz.2
    BR_jets := fun k hk z hz => full.BR_jets k hk z (ht hz)
    cutoff_jets := fun k hk z hz => full.cutoff_jets k hk z (ht hz)
    normal_jets := fun k hk z hz => full.normal_jets k hk z (ht hz) }
  · let Wn : Set (Ep × M) := {z | z.1 ∈ B.target ∧ (0,z.2) ∈ W}
    let κ : Wn → W := fun z => ⟨(0,z.val.2),z.property.2⟩
    have hκ : Continuous κ :=
      (continuous_const.prodMk continuous_subtype_val.snd).subtype_mk _
    have he : (Subtype.val ⁻¹' {z : Ep × M | z.1 ∈ B.target ∧ (0,z.2) ∈ K} : Set Wn) =
        κ ⁻¹' (Subtype.val ⁻¹' K : Set W) := by
      ext z
      change (z.val.1 ∈ B.target ∧ (0,z.val.2) ∈ K) ↔ (0,z.val.2) ∈ K
      exact and_iff_right z.property.1
    rw [he]
    exact raw.closed_support.preimage hκ
  · intro z hz hchi
    have hzB := ((passiveWaveSeed_native_target 0 B a z).mp hz).1
    rw [passiveWaveSeed_native_symm 0 B a z hzB]
    exact ⟨hzB,full.cutoff_support z (ht hz) hchi⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveWaveSeed_native_raw
