import Probes.ActualPreparedCompactParameterParents

/-! Actual compact source cutoffs follow from bounded original inner
coordinate pieces and their already existing buffer. No whole outer ball is
required inside a chart and no CompactSpace M assumption is introduced. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

omit [IsManifold 𝓘(ℝ,D) ∞ M] [BoundarylessManifold 𝓘(ℝ,D) M] in
theorem actual_raw_cutoff_compact_of_bounded_inner
    (A : BufferedAtlas M D) (B0 Ts : ℕ → ℝ) (degree : ℕ)
    (RS : TensorRawCutoffPreparation A B0 Ts degree)
    (centers : Fin A.count → D) (radius : ℝ)
    (hBound : ∀ i, (A.chart i) '' A.inner i ⊆ closedBall (centers i) radius)
    (i : Fin A.count) : IsCompact (tsupport (RS.raw i)) := by
  let C := closure ((A.chart i) '' A.inner i)
  have hC : IsCompact C := (isCompact_closedBall (centers i) radius).of_isClosed_subset
    isClosed_closure (closure_minimal (hBound i) isClosed_closedBall)
  have hCt : C ⊆ (A.chart i).target := by
    intro y hy
    obtain ⟨u,hu,hyu⟩ := Metric.mem_closure_iff.mp hy A.buffer A.buffer_pos
    obtain ⟨x,hx,rfl⟩ := hu
    exact A.buffered i x hx (mem_ball.mpr hyu)
  have hK : IsCompact ((A.chart i).symm '' C) :=
    hC.image_of_continuousOn ((A.chart i).symm.continuousOn.mono hCt)
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  have hxi := RS.inner_support i hx
  exact ⟨A.chart i x,subset_closure ⟨x,hxi,rfl⟩,(A.chart i).left_inv (A.inner_subset i hxi)⟩

theorem actual_original_compact_parameter_parents_from_coordinates
    (K Omega : Set Ep) (hK : IsCompact K) (hOmega : IsOpen Omega) (hKO : K ⊆ Omega)
    (B0 Ts : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B0 j) (hTs : ∀ j, 0 ≤ Ts j) (degree : ℕ) :
    ∃ (beta : Ep → ℝ) (V C : Set Ep) (Bbeta Bjoint : ℕ → ℝ),
      ContDiff ℝ ∞ beta ∧ IsOpen V ∧ K ⊆ V ∧ V ⊆ Omega ∧
      IsCompact C ∧ tsupport beta ⊆ C ∧ C ⊆ Omega ∧
      (∀ p ∈ V, beta p = 1) ∧ (∀ p, beta p ∈ Icc 0 1) ∧
      (∀ j, 0 ≤ Bbeta j) ∧ (∀ j p, ‖iteratedFDeriv ℝ j beta p‖ ≤ Bbeta j) ∧
      (∀ j, 0 ≤ Bjoint j) ∧ ∀ (A : BufferedAtlas M D) (_hA : IsSmoothBufferedAtlas A)
        (RS : TensorRawCutoffPreparation A B0 Ts degree)
        (centers : Fin A.count → D) (radius : ℝ)
        (_hBound : ∀ i, (A.chart i) '' A.inner i ⊆ closedBall (centers i) radius),
      let chi := squareNormalizedCutoff RS.raw
      let theta := fun i (z : Ep × M) => beta z.1 * chi i z.2 ^ 2
      (∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i)) ∧
      (∀ z, ∑ i, theta i z = beta z.1) ∧
      (∀ z : Ep × M, z.1 ∈ V → ∀ᶠ w in 𝓝 z, ∑ i, theta i w = 1) ∧
      (∀ i, tsupport (theta i) ⊆ C ×ˢ A.inner i) ∧
      (∀ i, IsCompact (tsupport (theta i))) ∧
      ∀ i j (ell : ℝ), 0 ≤ ell → ell ≤ 1 → ∀ z : X,
        z.2 ∈ bufferedInnerCoordinates A i → (A.chart i).symm z.2 ∈ tsupport (chi i) →
        ell^j*‖iteratedFDeriv ℝ j
          (theta i ∘ (actualOriginalHostJointChart («Ep» := Ep) (A.chart i)).symm) z‖ ≤ Bjoint j := by
  obtain ⟨beta,V,C,Bbeta,Bjoint,hBeta,hV,hKV,hVO,hC,hSupportBeta,hCO,hOne,hRange,
      hBbeta,hBetaJets,hBjoint,hPrepared⟩ :=
    actual_original_compact_parameter_parent_preparation (m := m) (d := d) (M := M)
      K Omega hK hOmega hKO B0 Ts hB0 hTs degree
  refine ⟨beta,V,C,Bbeta,Bjoint,hBeta,hV,hKV,hVO,hC,hSupportBeta,hCO,hOne,hRange,
    hBbeta,hBetaJets,hBjoint,?_⟩
  intro A hA RS centers radius hBound chi theta
  obtain ⟨hSmooth,hSum,hGerm,hSupport,hCompact,hJets⟩ := hPrepared A hA RS
  exact ⟨hSmooth,hSum,hGerm,hSupport,
    fun i => hCompact i (actual_raw_cutoff_compact_of_bounded_inner A B0 Ts degree RS
      centers radius hBound i),hJets⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_raw_cutoff_compact_of_bounded_inner

#print axioms GlobalEmbedding.Continuation.actual_original_compact_parameter_parents_from_coordinates
