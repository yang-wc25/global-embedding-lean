import Probes.ActualOriginalNativeTransitionJets
import Probes.ActualPositiveChartComposition
import Probes.ActualOriginalHostRefinement

/-!
# Actual original observer to produced adapted chart

The displayed transition is the literal host chart composed with the
original observer inverse. Original given-transition jets and the already
produced native chart's positive jets supply the full joint bound. The
sample set is unchanged, and no norm of a chart's value is required.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × Es

def actualOriginalObserverHostTransition
    (D : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) (host : Fin D.atlas.count) : X → X :=
  fun z => (z.1,D.atlas.chart host ((D.atlas.chart i.1).symm z.2))

omit [IsManifold 𝓘(ℝ,Es) ∞ M] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,Ep) ∞ P] in
theorem actualOriginalObserverHostTransition_eq
    (D : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) (host : Fin D.atlas.count) :
    EqOn (actualOriginalObserverHostTransition D i host)
      (actualOriginalNativeGivenTransition D i (host,i.2))
      (actualOriginalNativeGivenTransitionDomain D (i,(host,i.2))) := by
  intro z hz
  have hprod : (incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z),
      incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)) = z :=
    (parameterTensorModelEquiv (m+1) d).symm_apply_apply z
  have hp := congrArg Prod.fst hprod
  have hx := congrArg Prod.snd hprod
  dsimp only at hp hx
  have htarget : z.1 ∈ (D.parameterChart i.2).target := by
    simpa only [← hp] using hz.1.2
  simp only [actualOriginalObserverHostTransition,actualOriginalNativeGivenTransition,
    Function.comp_apply,actualOriginalGivenTransition,ContinuousLinearEquiv.symm_apply_apply]
  simp only [incrementsOriginalJointPoint,hp,hx,(D.parameterChart i.2).right_inv htarget]

theorem actual_original_observer_adapted_positive_jets
    (D : IncrementsOriginalNativeData (m+1) d N M P) (hd : IncrementsOriginalDomainConditions D)
    (i : Fin D.atlas.count × Fin D.parameterCount) (host : Fin D.atlas.count)
    (b : OpenPartialHomeomorph X X) (hb : ContDiffOn ℝ ∞ b b.source)
    (U S : Set X) (hU : IsOpen U) (hSU : S ⊆ U)
    (hOverlap : U ⊆ actualOriginalNativeGivenTransitionDomain D (i,(host,i.2)))
    (hMap : MapsTo (actualOriginalObserverHostTransition D i host) U b.source)
    (hSample : ∀ z ∈ S, parameterTensorModelEquiv (m+1) d z ∈
      actualOriginalGivenTransitionSample D (i,(host,i.2)))
    (j : ℕ) (ell budget Bnative : ℝ) (hell : 0 < ell) (hBnative : 0 ≤ Bnative)
    (hfinite : actualOriginalGivenInputProfile D j ell ≠ ⊤)
    (hbudget : (actualOriginalGivenInputProfile D j ell).toReal ≤ budget)
    (hNative : ∀ k, 1 ≤ k → k ≤ j+1 → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k b (actualOriginalObserverHostTransition D i host z)‖ ≤ Bnative) :
    let phi := fun z : X => (actualHostAdaptedChart (D.atlas.chart host) b)
      (z.1,(D.atlas.chart i.1).symm z.2)
    ContDiffOn ℝ ∞ phi U ∧
      ∀ k, 1 ≤ k → k ≤ j+1 → ∀ z ∈ S,
        ell^(k-1)*‖iteratedFDeriv ℝ k phi z‖ ≤
          actualFastChartTransferCost
            (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d j*budget) k*Bnative := by
  intro phi
  let T := actualOriginalObserverHostTransition D i host
  let V0 := actualOriginalNativeGivenTransitionDomain D (i,(host,i.2))
  have hV0 : IsOpen V0 := (actualOriginalGivenTransitionDomain_open D (i,(host,i.2))).preimage
    (parameterTensorModelEquiv (m+1) d).continuous
  have heq := actualOriginalObserverHostTransition_eq D i host
  have hT0 : ContDiffOn ℝ ∞ T V0 :=
    (actualOriginalNativeGivenTransition_contDiffOn D hd (i,(host,i.2))).congr heq
  have hT : ContDiffOn ℝ ∞ T U := hT0.mono hOverlap
  have hphi : phi = b ∘ T := rfl
  rw [hphi]
  refine ⟨hb.comp hT hMap,?_⟩
  intro k hk hkj z hz
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  have hcost0 : 0 ≤ actualOriginalNativeGivenTransitionJetCost (m+1) d j*budget :=
    mul_nonneg (actualOriginalNativeGivenTransitionJetCost_nonneg _ _ _) hbudget0
  apply actual_positive_joint_chart_composition
    (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d j*budget) (fun _ => hcost0)
    k hk T b U b.source hU b.open_source hT hb hMap z (hSU hz) ell Bnative hell hBnative
    (fun r hr hrk => hNative r hr (hrk.trans hkj) z hz)
  intro r hr hrk
  have hgerm : T =ᶠ[𝓝 z] actualOriginalNativeGivenTransition D i (host,i.2) := by
    filter_upwards [hV0.mem_nhds (hOverlap (hSU hz))] with w hw
    exact heq hw
  rw [(hgerm.iteratedFDeriv ℝ r).eq_of_nhds]
  have h := actual_original_given_native_transition_positive_jets D hd j ell budget hell hfinite hbudget
    (i,(host,i.2)) (r-1) (by omega) z (hSample z hz)
  have hrid : r-1+1 = r := by omega
  rwa [hrid] at h

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_observer_adapted_positive_jets
