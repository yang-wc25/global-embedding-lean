import FaithfulIncrements.OriginalQuantitativePrimaryRefinement
import OriginalIncrements.FiniteRefinementObserverBudget

/-!
# Original data produce a finite refinement and all named observer budgets

This is an actual original-data producer. It constructs one finite family
of native charts, genuine manifold slices and literal subordinate cutoffs
before every observation order and scale. It retains the original primary
supports, partition germs and dimension-only local multiplicity. The same
family then satisfies explicit positive forward and inverse observer costs
in every original observing chart, using only the original Given prefix
through j - 1 and the original transition prefix through j.

The low-order constants mu, Mb and buffer are actual outputs of the original
compact phase construction. This theorem does not exchange fixed-data
existence for class-uniform estimates of those constants; that remaining
quantitative obligation is stated rather than added as a premise.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [T2Space M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem original_primary_refinement_with_finite_observer_budgets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hParam : ∀ w ∈ W, w.1 ∈ (Data.parameterChart i.2).target)
    (hOriginal : MapsTo (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2))
      W (incrementsOriginalParameterRegion Data))
    (theta : Ep × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hTheta : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta)
    (hThetaSupport : tsupport theta ⊆ W ∩
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source) :
    ∃ (mu Mb buffer : ℝ) (s : Finset X) (b : s → OpenPartialHomeomorph X X)
      (e : s → Ep → OpenPartialHomeomorph M D) (eta : s → Ep × M → ℝ) (Bnative : ℝ),
      0 < mu ∧ 0 ≤ Mb ∧ 0 < buffer ∧ Bnative = 2*(1+2*Mb) ∧ 0 < Bnative ∧
      (∀ a : s, ActualOriginalHostSliceData (Data.atlas.chart i.1) (b a)
        (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e a)) ∧
      (∀ a : s, (b a).source ⊆ actualOriginalNativeOpen Data i) ∧
      (∀ a : s, (actualHostAdaptedChart (Data.atlas.chart i.1) (b a)).source ⊆ W) ∧
      (∀ a : s, ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) (b a)).source,
        ((Data.parameterChart i.2).symm w.1,w.2) ∈
          Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ a : s, IsCompact (tsupport (eta a))) ∧
      (∀ a : s, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (eta a)) ∧
      (∀ a : s, tsupport (eta a) ⊆
        (actualHostAdaptedChart (Data.atlas.chart i.1) (b a)).source ∩ tsupport theta) ∧
      (∀ y ∈ incrementsGlobalRelativeSupport W
          (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)),
        ∑ a : s, eta a y = theta y) ∧
      (∀ y ∈ incrementsGlobalRelativeSupport W
          (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)),
        ∀ᶠ w in 𝓝 y, ∑ a : s, eta a w = theta w) ∧
      (∀ y, (Finset.univ.filter (fun a : s => y ∈ tsupport (eta a))).card ≤ 5^Module.finrank ℝ X) ∧
      (∀ a : s, ∀ z ∈ (b a).source, ‖fderiv ℝ (b a) z‖ ≤ Bnative) ∧
      (∀ a : s, eta a = actualHostRefinementCutoff
        (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) theta
        (actualRefinementCutoff X s (buffer/actualPhaseRefinementFactor mu Mb) a.val)) ∧
      (∀ (j : ℕ) (weight : ℝ), 0 ≤ weight → weight ≤ buffer → ∀ (a : s) (x : X),
        weight^j*‖iteratedFDeriv ℝ j
          (actualRefinementCutoff X s (buffer/actualPhaseRefinementFactor mu Mb) a.val) x‖ ≤
          (actualPhaseRefinementFactor mu Mb)^j * actualRefinementCutoffJetCost X j) ∧
      (∀ (a : s) k, 1 ≤ k → ∀ x ∈ (b a).source,
        ‖iteratedFDeriv ℝ (k+1) (b a) x‖ ≤
          2^(k+2)*‖iteratedFDeriv ℝ (k+1)
            ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘
              (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) x‖) ∧
      (∀ (a : s) (S : Set X), S ⊆ (b a).target → ∀ (j : ℕ) (weight Mj : ℝ),
        0 < weight → 0 ≤ Mj →
        (∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ (b a).symm '' S,
          weight^k*‖iteratedFDeriv ℝ (k+1)
            ((fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘
              (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) x‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ S,
          weight^(k-1)*‖iteratedFDeriv ℝ k (b a).symm y‖ ≤
            actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j) ∧
      (∀ a : s, OriginalRefinementObserverBudgets Data i nu mu Mb (b a)) := by
  obtain ⟨mu,Mb,buffer,s,b,e,eta,Bnative,hmu,hMb,hbuffer,hB,hBpos,
    hData,hOpen,hWsource,hActive,hCompactEta,hSmoothEta,hSupportEta,hPartition,hGerm,
    hCount,hNative,hCutoffEq,hCutoffJets,hHigher,hInverse⟩ :=
    FaithfulIncrements.original_quantitative_primary_refinement
      Data hd hs hp i nu W hW hParam hOriginal theta hCompact hTheta hThetaSupport
  refine ⟨mu,Mb,buffer,s,b,e,eta,Bnative,hmu,hMb,hbuffer,hB,hBpos,
    hData,hOpen,hWsource,hActive,hCompactEta,hSmoothEta,hSupportEta,hPartition,hGerm,
    hCount,hNative,hCutoffEq,hCutoffJets,hHigher,hInverse,?_⟩
  intro a
  exact original_refinement_observer_budgets_of_actual_jets Data hd hs i nu mu Mb hmu hMb
    (b a) (e a) (hData a) (by simpa only [hB] using hNative a)
    (hHigher a) (hInverse a)

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_primary_refinement_with_finite_observer_budgets
