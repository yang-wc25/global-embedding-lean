import CompletionIntegration.CompactCutoffObserverProfiles
import Probes.Round3PreparedParameterSecondaryPieces

/-!
# The actual packet manufactures its observer-cutoff profile

The physical packet and all original observation domains are fixed literally.
Compactness belongs to each already constructed physical cutoff. The original
transition budgets transport its host jets only on the active support. The
resulting one profile covers all observers, all orders and every later scale.
This theorem does not claim finite-prefix uniformity of the qualitative
adapted-piece construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance : ChartedSpace X (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M
private local instance signedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem prepared_secondary_original_observer_cutoff_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆
      (Data.parameterChart i.2).source ×ˢ Data.atlas.inner i.1)
    (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial) :
    ∃ Kcut : ℕ → ℝ, (∀ n, 0 ≤ Kcut n) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ r i (a : packet.s r i) observer n k, k ≤ n →
        let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
        ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
          Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
          ell^k * ‖iteratedFDeriv ℝ k (fun y : X => choice.cutoff
            ((Data.parameterChart observer.2).symm y.1,(Data.atlas.chart observer.1).symm y.2)) z‖ ≤ Kcut n := by
  let A := Sigma (fun r : ActualSecondarySignedRecord (Fin Data.primaryCount) =>
    Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(packet.s r i)))
  let J := A × (Fin Data.atlas.count × Fin Data.parameterCount)
  let q := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    (Data.parameterChart i.2).prod (Data.atlas.chart i.1)
  have hq (i) : q i ∈ maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hd.parameter_charts_smooth i.2)
      (hd.atlas_smooth.chart_mem i.1)
  let Sn := fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹'
    incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i
  have hSn (i) : Sn i ⊆ (q i).target := by
    intro z hz
    have h := (actual_original_native_evaluation_iff Data hd i z).mp hz
    exact ⟨hd.parameter_norm_subset i.2 h.2.1,hd.source_norm_subset i.1 h.1⟩
  let rho := fun a : A =>
    (round3PreparedParameterSecondaryChoice Data hd hs a.2.1 a.1 _ (packet.piece a.1 a.2.1 a.2.2)).cutoff
  have hRho (a : A) : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,ℝ) ∞ (rho a) := by
    rw [modelWithCornersSelf_prod]
    exact packet.smooth a.1 a.2.1 a.2.2
  have hRhoSupport (a : A) : tsupport (rho a) ⊆ (q a.2.1).source := by
    intro y hy
    have h := hSupport a.2.1 (packet.parent a.1 a.2.1 a.2.2 hy)
    exact ⟨h.1,Data.atlas.inner_subset a.2.1.1 h.2⟩
  let T := fun k => max (Parameter k) (Spatial k)
  have hT : ∀ k, 0 ≤ T k := fun k => (hParameter k).trans (le_max_left _ _)
  have hOne (j : J) := completion_compact_cutoff_observer_profiles
    (q j.1.2.1) (q j.2) (hq j.1.2.1) (hq j.2) (rho j.1) (hRho j.1)
    (packet.compact j.1.1 j.1.2.1 j.1.2.2) (hRhoSupport j.1) (Sn j.2) (hSn j.2)
    T hT (by
      intro z hz hActive k hk
      have hPhysical : ((Data.parameterChart j.2.2).symm z.1,
          (Data.atlas.chart j.2.1).symm z.2) ∈ (q j.1.2.1).source := hRhoSupport j.1 hActive
      have hpair : (incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z),
          incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)) = z :=
        (parameterTensorModelEquiv (m+1) d).symm_apply_apply z
      have hp := congrArg Prod.fst hpair
      have hx := congrArg Prod.snd hpair
      dsimp only at hp hx
      have hSample : parameterTensorModelEquiv (m+1) d z ∈
          actualOriginalGivenTransitionSample Data (j.2,j.1.2.1) := by
        refine ⟨hz,hz.1,?_⟩
        change (Data.parameterChart j.2.2).symm
            (incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z)) ∈
            (Data.parameterChart j.1.2.1.2).source ∧
          (Data.atlas.chart j.2.1).symm
            (incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)) ∈
            (Data.atlas.chart j.1.2.1.1).source
        rw [hp,hx]
        exact hPhysical
      have h := (increment_given_actual_native_transition_jets Data hd Parameter Spatial transition
        (j.2,j.1.2.1) (parameterTensorModelEquiv (m+1) d z) hSample k hk).2
      have hFun : (q j.1.2.1) ∘ (q j.2).symm = (fun w : X =>
          (Data.parameterChart j.1.2.1.2 ((Data.parameterChart j.2.2).symm w.1),
            Data.atlas.chart j.1.2.1.1 ((Data.atlas.chart j.2.1).symm w.2))) := by
        funext w
        rfl
      rw [hFun]
      simpa only [ContinuousLinearEquiv.symm_apply_apply,T] using h)
  choose C hC hBound using hOne
  let Kcut := fun n => round3PreparedFiniteMaximum (fun j : J × Fin (n+1) => C j.1 j.2)
  refine ⟨Kcut,fun n => round3PreparedFiniteMaximum_nonneg _,?_⟩
  intro ell hell hell1 r i a observer n k hkn choice z hz
  exact (hBound (⟨r,⟨i,a⟩⟩,observer) ell hell hell1 k z hz).trans
    (round3PreparedFiniteMaximum_bound (fun j : J × Fin (n+1) => C j.1 j.2)
      ((⟨r,⟨i,a⟩⟩,observer),⟨k,Nat.lt_succ_of_le hkn⟩))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.prepared_secondary_original_observer_cutoff_profiles
