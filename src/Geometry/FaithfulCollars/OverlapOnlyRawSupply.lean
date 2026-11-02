import FaithfulCollars.UniformManifoldRepairSupply

/-!
# Original raw supply needs parameter transitions only on genuine overlaps

The original norm cover already lands in each chart target. Intersecting
an auxiliary enlarged support with the corresponding chart source keeps
that cover and decreases the intersection degree. This supplies the same
primitive numerical budget and original-domain carriers from transition
bounds only where both coordinate charts are genuinely defined.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.FaithfulCollars
open SourceCollarsBridge
universe uM uP

theorem OriginalParameterNormBuffer.inter_chart_source
    {E P ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace P]
    {chart : ι → OpenPartialHomeomorph P E} {Q : ι → Set E} {W : ι → Set P}
    {K : Set P} {R b : ℝ} (g : OriginalParameterNormBuffer chart Q W K R b) :
    OriginalParameterNormBuffer chart Q (fun i => W i ∩ (chart i).source) K R b := by
  refine ⟨g.radius_pos, g.norm_target, g.norm_radius, ?_⟩
  intro p hp
  obtain ⟨i, hi, hball⟩ := g.cover p hp
  refine ⟨i, hi, ?_⟩
  intro y hy
  have h := hball hy
  exact ⟨h.1, h.2, (chart i).map_target (g.norm_target i h.1)⟩

theorem fixedOriginalPrimitiveGeometryBudget_supply_on_overlaps
    (n d : ℕ) (RSrc bSrc RPar bPar : ℝ) (hbSrc : 0 < bSrc) (hbPar : 0 < bPar)
    (TS TP PT ST : ℕ → ℝ) (hTS : ∀ j, 0 ≤ TS j) (hTP : ∀ j, 0 ≤ TP j)
    (hPT : ∀ j, 0 ≤ PT j) (hST : ∀ j, 0 ≤ ST j) (Ds Dp : ℕ) :
    let b := fixedOriginalPrimitiveGeometryBudget n d RSrc bSrc RPar bPar hbSrc hbPar
      TS TP PT ST hTS hTP hPT hST Ds Dp
    ∀ (M : Type uM) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
      (P : Type uP) [TopologicalSpace P] [T2Space P]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P],
      ∀ (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))) (Omega : Fin A.count → Set (EuclideanSpace ℝ (Fin n)))
        (_gS : OriginalSourceNormBuffer A Omega RSrc bSrc)
        (pc : ℕ) (chart : Fin pc → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
        (Q : Fin pc → Set (EuclideanSpace ℝ (Fin d))) (W : Fin pc → Set P),
      OriginalParameterNormBuffer chart Q W univ RPar bPar →
      IsSmoothBufferedAtlas A →
      (∀ i, chart i ∈ maximalAtlas 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P) →
      A.supportDegree ≤ Ds →
      (∀ i, tensorEnlargedSupportDegree W i ≤ Dp) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (A.chart p).target,
        (A.chart p).symm y ∈ A.support i →
        ‖iteratedFDeriv ℝ j (A.chart i ∘ (A.chart p).symm) y‖ ≤ TS j) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (chart p).target,
        (chart p).symm y ∈ W i → (chart p).symm y ∈ (chart i).source →
        ‖iteratedFDeriv ℝ j (chart i ∘ (chart p).symm) y‖ ≤ TP j) →
      OriginalParameterJointTransitions (n := n) chart Q PT →
      OriginalSpatialJointTransitions (d := d) A Omega ST →
      ∃ g : SourceCollarNovSetup n d M P,
        ∃ hSourceCount : g.source.count = A.count,
          ∃ hParameterCount : g.parameter.count = pc,
          (∀ i, g.source.chart i = A.chart (Fin.cast hSourceCount i)) ∧
          (∀ i, g.parameter.chart i = chart (Fin.cast hParameterCount i)) ∧
          (∀ i, g.source.support i = A.support (Fin.cast hSourceCount i)) ∧
          (∀ i, g.parameter.support i ⊆ W (Fin.cast hParameterCount i)) ∧
          (∀ i, g.Omega i ⊆ Omega (Fin.cast hSourceCount i)) ∧
          (∀ i, g.Q i ⊆ Q (Fin.cast hParameterCount i)) ∧
          g.source.buffer = b.sourceBuffer ∧ g.parameter.buffer = b.parameterBuffer ∧
          PrimitiveGeometryBounds b g := by
  intro b M _ _ _ _ P _ _ _ _
  intro A Omega gS pc chart Q W gP hA hChart hDs hDp hSTrans hPTrans hPJoint hSJoint
  let W' := fun i => W i ∩ (chart i).source
  have hDp' : ∀ i, tensorEnlargedSupportDegree W' i ≤ Dp := fun i =>
    (enlargedSupportDegree_mono W' W (fun _ => inter_subset_left) i).trans (hDp i)
  obtain ⟨g, hs, hp, hSchart, hPchart, hSsupport, hPsupport, hOmega, hQ,
    hSbuffer, hPbuffer, hg⟩ :=
    fixedOriginalPrimitiveGeometryBudget_supply n d RSrc bSrc RPar bPar hbSrc hbPar
      TS TP PT ST hTS hTP hPT hST Ds Dp M P A Omega gS pc chart Q W'
      gP.inter_chart_source hA hChart hDs hDp' hSTrans
      (fun p i j hj y hy hi => hPTrans p i j hj y hy hi.1 hi.2) hPJoint hSJoint
  exact ⟨g, hs, hp, hSchart, hPchart, hSsupport,
    fun i => (hPsupport i).trans inter_subset_left, hOmega, hQ, hSbuffer, hPbuffer, hg⟩

end GlobalEmbedding.Continuation.FaithfulCollars

#print axioms GlobalEmbedding.Continuation.FaithfulCollars.fixedOriginalPrimitiveGeometryBudget_supply_on_overlaps
