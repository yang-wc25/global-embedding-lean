import UpgradeContinuation.ZeroParameterAtlas
import NormalPolar.PassiveOriginalParameterPrepared
import Repair.SourceCollarNovSetup

/-!
# Actual fixed reference geometry for an unparameterized source

The compact source supplies its finite prepared atlas, compact norm domains,
and all-order raw profiles.  Compactness of the actual norm domains also
supplies all positive-order original transition profiles.  The parameter
factor is the literal identity atlas on dimension zero.  Thus the fixed
Setup needed by the existing native-data and smoothing factories is made
from the manifold rather than requested as a probe hypothesis.
-/

noncomputable section
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical BigOperators

namespace GlobalEmbedding.Continuation.UpgradeContinuation

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Z" => ZeroParameter

/-- Compact coordinate domains and globally smooth forward coordinates
give actual all-order transition bounds, including near another chart's
source boundary.  The bounds are chosen once before the order is queried. -/
theorem compactSource_transition_profiles
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,D) ∞ (A.chart i))
    (Omega : Fin A.count → Set D)
    (hcompact : ∀ i, IsCompact (Omega i))
    (htarget : ∀ i, Omega i ⊆ (A.chart i).target) :
    ∃ T : ℕ → ℝ, (∀ k, 0 ≤ T k) ∧
      ∀ i j k y, y ∈ Omega i →
        ‖iteratedFDeriv ℝ k (A.chart j ∘ (A.chart i).symm) y‖ ≤ T k := by
  have hbound : ∀ i j k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Omega i,
      ‖iteratedFDeriv ℝ k (A.chart j ∘ (A.chart i).symm) y‖ ≤ C := by
    intro i j k
    have hf : ContDiffOn ℝ ∞ (A.chart j ∘ (A.chart i).symm) (A.chart i).target :=
      ((hforward j).comp_contMDiffOn
        (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))).contDiffOn
    obtain ⟨C,hC⟩ := parameterRound2_coordinate_jets_bounded_of_compact
      (A.chart j ∘ (A.chart i).symm) (A.chart i).target (Omega i) (Omega i)
      (A.chart i).open_target (hcompact i) Subset.rfl (htarget i) hf k
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro y hy
    exact (hC ⟨⟨y,hy⟩,rfl⟩).trans (le_max_left _ _)
  choose C hC hboundC using hbound
  refine ⟨fun k => ∑ i, ∑ j, C i j k,
    fun k => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC i j k)),?_⟩
  intro i j k y hy
  exact (hboundC i j k y hy).trans
    ((Finset.single_le_sum (fun j' _ => hC i j' k) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i' _ => Finset.sum_nonneg (fun j' _ => hC i' j' k))
        (Finset.mem_univ i)))

/-- A complete fixed geometric Setup is constructed for the reference map.
The one reference parameter chart remains definitionally the identity. -/
theorem exists_zeroParameter_compactSetup :
    ∃ g : SourceCollarNovSetup n 0 M Z,
      g.parameter = zeroParameterAtlas ∧
      g.Q = (fun _ => univ) ∧
      (∀ i, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,D) ∞ (g.source.chart i)) ∧
      (∀ i, IsCompact (g.source.support i)) ∧
      (∀ x, ∃ i, x ∈ g.source.support i) := by
  obtain ⟨A0,hA0,hforward,Omega,hOmega,BS,TS,hBS,hTS,⟨RS0⟩⟩ :=
    passiveOriginal_exists_global_forward_prepared_parameter_atlas (d := n) (P := M)
  let A : BufferedAtlas M D := { A0 with support := fun i => (A0.chart i).symm '' Omega i }
  have hinner (i : Fin A.count) : A.inner i ⊆ A.support i := by
    intro x hx
    refine ⟨A0.chart i x,?_,(A0.chart i).left_inv (A0.inner_subset i hx)⟩
    exact (hOmega i).2.2 (subset_closure
      (bufferedInner_subset_sampling A0 i (bufferedInnerCoordinates_mem A0 i hx)))
  have hA : IsSmoothBufferedAtlas A := {
    chart_mem := hA0.chart_mem
    support_subset := by
      intro i x hx
      obtain ⟨y,hy,rfl⟩ := hx
      exact (A0.chart i).map_target ((hOmega i).2.1 hy) }
  have hAcompact (i : Fin A.count) : IsCompact (A.support i) :=
    (hOmega i).1.image_of_continuousOn ((A0.chart i).continuousOn_symm.mono (hOmega i).2.1)
  have hAcover (x : M) : ∃ i, x ∈ A.support i := by
    obtain ⟨i,hi⟩ := A.cover x
    exact ⟨i,hinner i hi⟩
  let RS : TensorRawCutoffPreparation A BS TS A.supportDegree := {
    raw := RS0.raw
    smooth := RS0.smooth
    plateau_cover := RS0.plateau_cover
    inner_support := RS0.inner_support
    enlarged_support := fun i => (RS0.inner_support i).trans (hinner i)
    degree := le_rfl
    own_jets := RS0.own_jets
    transition_jets := RS0.transition_jets }
  obtain ⟨T,hT,htrans⟩ := compactSource_transition_profiles A hA hforward Omega
    (fun i => (hOmega i).1) (fun i => (hOmega i).2.1)
  have hbound : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Omega i, ‖y‖ ≤ C := by
    intro i
    obtain ⟨C,hC⟩ := (hOmega i).1.exists_bound_of_continuousOn
      (continuous_id : Continuous (id : D → D)).continuousOn
    exact ⟨max C 0,le_max_right _ _,fun y hy => (hC y hy).trans (le_max_left _ _)⟩
  choose C hC hboundC using hbound
  let R : ℝ := ∑ i, C i
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => hC i)
  have hcoords (i) (y : D) (hy : y ∈ Omega i) : ‖y‖ ≤ R :=
    (hboundC i y hy).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))
  let g : SourceCollarNovSetup n 0 M Z := {
    source := A
    parameter := zeroParameterAtlas
    source_smooth := hA
    parameter_smooth := zeroParameterAtlas_smooth
    BS := BS
    TS := TS
    BP := fun _ => 1
    TP := fun _ => 1
    BS_nonneg := hBS
    TS_nonneg := hTS
    BP_nonneg := fun _ => zero_le_one
    TP_nonneg := fun _ => zero_le_one
    Ds := A.supportDegree
    Dp := zeroParameterAtlas.supportDegree
    sourcePreparation := RS
    parameterPreparation := zeroParameterRaw
    Omega := Omega
    Q := fun _ => univ
    source_compact := fun i => (hOmega i).1
    parameter_compact := fun _ => zeroParameterAtlas_compact
    source_target := fun i => (hOmega i).2.1
    parameter_target := fun _ => Subset.rfl
    source_sampling := fun i => subset_closure.trans (hOmega i).2.2
    parameter_sampling := fun _ => subset_univ _
    coordinateRadius := R
    coordinateRadius_nonneg := hR
    source_bound := hcoords
    parameter_bound := by
      intro i p hp
      rw [zeroParameterAtlas_norm]
      exact hR
    parameterTransition := fun _ => 1
    spatialTransition := fun k => max 1 (T k)
    parameterTransition_nonneg := fun _ => zero_le_one
    spatialTransition_nonneg := fun k => zero_le_one.trans (le_max_left _ _)
    parameter_transition_jets := by
      intro ip jp k hk z hz hs
      exact round4_positive_identity_jet_norm_le k hk z
    spatial_transition_jets := by
      intro i j k hk z hz hs
      change ‖iteratedFDeriv ℝ k
        (fun y : Z × D => (y.1, A.chart j ((A.chart i).symm y.2))) z‖ ≤ max 1 (T k)
      have hf : ContDiffOn ℝ ∞ (A.chart j ∘ (A.chart i).symm) (A.chart i).target :=
        ((hforward j).comp_contMDiffOn
          (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))).contDiffOn
      exact tensor_product_map_jet_le isOpen_univ (A.chart i).open_target
        contDiff_id.contDiffOn hf (mem_univ z.1) ((hOmega i).2.1 hz) k 1 (T k)
        (round4_positive_identity_jet_norm_le k hk z.1) (htrans i j k z.2 hz) }
  exact ⟨g,rfl,rfl,hforward,hAcompact,hAcover⟩

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.compactSource_transition_profiles
#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.exists_zeroParameter_compactSetup
