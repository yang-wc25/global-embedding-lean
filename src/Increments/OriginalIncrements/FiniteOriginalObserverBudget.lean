import OriginalIncrements.FinitePhaseProfileSupplier
import IncrementsCompletion.PositiveWeightedObserverFiniteJets
import Probes.ActualAdaptedChartHost

/-!
# Original host phase jets produce the actual observer budgets

The local adapted chart and its manifold slices are constructed internally
from the original phase on the original host ball.  The output bounds the
actual observing-chart transition and its inverse at the original sample.
Only the original phase prefix at the same actual host point and the original
coordinate-transition budgets occur in its quantitative assumptions.

The low-order ball/noncriticality input is a local supplier input.  Obtaining
it uniformly from the full original setup remains a separate geometric step;
this theorem does not silently add it to the original global lemma.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements

def phaseObserverForwardBudget (_mu M : ℝ) (Phase Parameter Spatial : ℕ → ℝ) : ℕ → ℝ :=
  incrementsCompletionPositiveObserverForwardProfile (phaseForwardBudget M Phase) Parameter Spatial

def phaseObserverInverseBudget (mu M : ℝ) (Phase Parameter Spatial : ℕ → ℝ) : ℕ → ℝ :=
  incrementsCompletionPositiveObserverInverseProfile (phaseInverseBudget mu M Phase) Parameter Spatial

theorem phase_observer_budgets_mono_prefix
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (Phase Parameter Spatial Phase' Parameter' Spatial' : ℕ → ℝ)
    (hPhase : ∀ k, 1 ≤ k → 0 ≤ Phase k)
    (hParameter : ∀ k, 1 ≤ k → 0 ≤ Parameter k)
    (hSpatial : ∀ k, 1 ≤ k → 0 ≤ Spatial k) (j : ℕ)
    (hPh : ∀ k, 1 ≤ k → k ≤ j → Phase k ≤ Phase' k)
    (hPa : ∀ k, 1 ≤ k → k ≤ j → Parameter k ≤ Parameter' k)
    (hSp : ∀ k, 1 ≤ k → k ≤ j → Spatial k ≤ Spatial' k) :
    phaseObserverForwardBudget mu M Phase Parameter Spatial j ≤
      phaseObserverForwardBudget mu M Phase' Parameter' Spatial' j ∧
    phaseObserverInverseBudget mu M Phase Parameter Spatial j ≤
      phaseObserverInverseBudget mu M Phase' Parameter' Spatial' j := by
  apply positive_observer_profiles_mono_prefix
    (phaseForwardBudget M Phase) (phaseInverseBudget mu M Phase) Parameter Spatial
    (phaseForwardBudget M Phase') (phaseInverseBudget mu M Phase') Parameter' Spatial' j
    (fun k _ => phaseForwardBudget_nonneg M hM Phase hPhase k)
    (fun k _ => phaseInverseBudget_nonneg mu M hmu hM Phase hPhase k)
    hParameter hSpatial _ _ hPa hSp
  · intro k hk hkj
    exact (phase_profiles_mono_prefix mu M hmu hM Phase Phase' hPhase k
      (fun l hl hlk => hPh l hl (hlk.trans hkj))).1
  · intro k hk hkj
    exact (phase_profiles_mono_prefix mu M hmu hM Phase Phase' hPhase k
      (fun l hl hlk => hPh l hl (hlk.trans hkj))).2

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

/-- The same actual native chart and actual slices work for all later
orders and original samples. There is no native forward/inverse profile or
observer estimate among the inputs. -/
theorem exists_original_observer_from_finite_phase_budgets
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    (ip : Fin Ref.parameterCount) (host : Fin Ref.atlas.count)
    (psi : Ep × M → ℝ) (z0 : X) (rho mu Mb : ℝ)
    (hrho : 0 < rho) (hmu : 0 < mu) (hMb : 0 ≤ Mb)
    (hBall : ball z0 rho ⊆ (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart host)).target)
    (hPsi : ContDiffOn ℝ ∞
      (psi ∘ (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart host)).symm) (ball z0 rho))
    (hNoncritical : mu ≤ ‖(fderiv ℝ
      (psi ∘ (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart host)).symm) z0).comp
        (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hFirst : ∀ z ∈ ball z0 rho, ‖fderiv ℝ
      (psi ∘ (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart host)).symm) z‖ ≤ Mb)
    (hSecond : ∀ z ∈ ball z0 rho, rho*‖iteratedFDeriv ℝ 2
      (psi ∘ (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart host)).symm) z‖ ≤ Mb) :
    ∃ (native : OpenPartialHomeomorph X X) (slices : Ep → OpenPartialHomeomorph M D),
      ball z0 (actualEuclideanPhaseRadius mu Mb rho) ⊆ native.source ∧
      native.source ⊆ ball z0 rho ∧
      ActualOriginalHostSliceData (Ref.atlas.chart host) native psi slices ∧
      Round3ParameterChartPreserves native ∧
      ∀ (Phase Parameter Spatial : ℕ → ℝ),
        (∀ k, 1 ≤ k → 0 ≤ Phase k) →
        (∀ k, 1 ≤ k → 0 ≤ Parameter k) →
        (∀ k, 1 ≤ k → 0 ≤ Spatial k) →
        RepairOriginalTransitionBudgets Ref Parameter Spatial →
        ∀ (ell : ℝ), 0 < ell → ell ≤ 1 →
        ∀ (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (z : X),
          z.1 ∈ Ref.parameterNormDomain i.2 → z.2 ∈ Ref.sourceNormDomain i.1 →
          Ref.parameterChart ip ((Ref.parameterChart i.2).symm z.1) ∈ Ref.parameterNormDomain ip →
          Ref.atlas.chart host ((Ref.atlas.chart i.1).symm z.2) ∈ Ref.sourceNormDomain host →
          let point := incrementsCompletionOriginalHostPoint Ref ip host i z
          let b := round3ParameterCrossNativeChart (Ref.parameterChart ip) (Ref.parameterChart i.2) native
          let t := ((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart i.1)).symm.trans
            (actualHostAdaptedChart (Ref.atlas.chart host) b)
          z ∈ t.source → ∀ j, 1 ≤ j →
          (∀ k, 2 ≤ k → k ≤ j →
            ell^(k-1)*‖iteratedFDeriv ℝ k
              (psi ∘ (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart host)).symm) point‖ ≤ Phase k) →
          ell^(j-1)*‖iteratedFDeriv ℝ j t z‖ ≤ phaseObserverForwardBudget mu Mb Phase Parameter Spatial j ∧
          ell^(j-1)*‖iteratedFDeriv ℝ j t.symm (t z)‖ ≤ phaseObserverInverseBudget mu Mb Phase Parameter Spatial j := by
  let q := actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart host)
  let Psi := psi ∘ q.symm
  obtain ⟨a,hi,ho,ha,hai,hp,hpi,ht,hBudget⟩ :=
    exists_actual_chart_with_finite_phase_budgets mu Mb hmu hMb Psi z0 rho hrho
      hPsi hNoncritical hFirst hSecond
  obtain ⟨hat,haM,haiM,hpM,slices,hslices⟩ :=
    actual_adapted_chart_original_host (Ref.atlas.chart host) (hd.atlas_smooth.chart_mem host)
      psi a (ho.trans hBall) ha hai (fun z hz => (hp z hz).1) (fun z hz => (hp z hz).2)
  have hData : ActualOriginalHostSliceData (Ref.atlas.chart host) a psi slices :=
    ⟨hat,haM,haiM,hpM,hslices⟩
  have hPreserves : Round3ParameterChartPreserves a := fun z hz => (hp z hz).1
  refine ⟨a,slices,hi,ho,hData,hPreserves,?_⟩
  intro Phase Parameter Spatial hPhase hParameter hSpatial transition ell hell hell1
    i z hzP hzX hOwnP hOwnX point b t hzt j hj hPhaseJets
  have hPoint : point ∈ a.source := by
    have hzB := hzt.2.2
    have hn := (round3ParameterChartPullback_source
      ((Ref.parameterChart ip).symm.trans (Ref.parameterChart i.2)) a
      (z.1,(Ref.atlas.chart host) ((Ref.atlas.chart i.1).symm z.2))).mp hzB
    exact hn.2.1
  have hSample (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      ell^(k-1)*‖iteratedFDeriv ℝ k a point‖ ≤ phaseForwardBudget Mb Phase k ∧
      ell^(k-1)*‖iteratedFDeriv ℝ k a.symm (a point)‖ ≤ phaseInverseBudget mu Mb Phase k := by
    have hSet : ({a point} : Set X) ⊆ a.target :=
      singleton_subset_iff.mpr (a.map_source hPoint)
    have hPointSet : point ∈ a.symm '' ({a point} : Set X) :=
      ⟨a point,mem_singleton _,a.left_inv hPoint⟩
    have hJets : ∀ l, 2 ≤ l → l ≤ k → ∀ x ∈ a.symm '' ({a point} : Set X),
        ell^(l-1)*‖iteratedFDeriv ℝ l Psi x‖ ≤ Phase l := by
      intro l hl hlk x hx
      obtain ⟨y,hy,rfl⟩ := hx
      have hyEq : y = a point := mem_singleton_iff.mp hy
      rw [hyEq,a.left_inv hPoint]
      exact hPhaseJets l hl (hlk.trans hkj)
    have hh := hBudget {a point} hSet ell Phase hell hPhase k hk hJets
    exact ⟨hh.1 point hPointSet,hh.2 (a point) (mem_singleton _)⟩
  exact incrementsCompletion_original_native_observer_finite_weighted_jets_at
    Ref hd ip host a psi slices hData hPreserves
    (phaseForwardBudget Mb Phase) (phaseInverseBudget mu Mb Phase) Parameter Spatial
    (fun k _ => phaseForwardBudget_nonneg Mb hMb Phase hPhase k)
    (fun k _ => phaseInverseBudget_nonneg mu Mb hmu hMb Phase hPhase k)
    hParameter hSpatial transition ell hell hell1 i z hzP hzX hOwnP hOwnX j hj
    (fun k hk hkj => (hSample k hk hkj).1)
    (fun k hk hkj => (hSample k hk hkj).2) hzt

end GlobalEmbedding.Continuation.OriginalIncrements

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.phase_observer_budgets_mono_prefix
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.exists_original_observer_from_finite_phase_budgets
