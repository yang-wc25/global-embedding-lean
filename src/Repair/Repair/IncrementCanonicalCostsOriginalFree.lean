import Smoothing.ParameterRound2OriginalFreeIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
universe uCanonicalM

variable {E H Ep T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem incrementCanonical_parameterRound2_original_primary_free_jets_uniform_index
    (n : ℕ) (c Bnd : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ (M : Type uCanonicalM) [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [BoundarylessManifold I M], ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β] (F : Ep → M → V)
      (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (ν : Λ) (β : Β) (S : Set X) (hSO : S ⊆ (g.chart ν β).target)
      (L : X → T →L[ℝ] ℝ) (A : X → T)
      (hL : ContDiffOn ℝ ∞ L (g.chart ν β).target)
      (hA : ContDiffOn ℝ ∞ A (g.chart ν β).target)
      (hRep : ∀ z ∈ (g.chart ν β).target,
        L z (A z) = g.linearArgument ν z.1 (g.inverse ν β z.1 z.2)
          (input z.1 (g.inverse ν β z.1 z.2)))
      (hCut : ContDiffOn ℝ ∞ (fun z : X => g.cutoff ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (hEta : ContDiffOn ℝ ∞ (fun z : X => g.eta ν β (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (hNormal : ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (ell tau : ℝ) (hell : 0 < ell) (htau : 0 ≤ tau)
      (hReserve : ∀ z ∈ S, c ≤ L z (A z))
      (hLb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r L z‖ ≤ Bnd)
      (hAb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r A z‖ ≤ Bnd)
      (hCutb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.cutoff ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
      (hEtab : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.eta ν β (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
      (hNormalb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.normal ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd),
    ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 : V)) z‖ ≤ K*tau := by
  obtain ⟨K,hK,hb⟩ := actual_subordinate_primary_free_jets_uniform n c Bnd hc hBnd
  refine ⟨K,hK,?_⟩
  intro M _ _ _ _
  intro Λ Β _ _ F g input ν β S hSO L A hL hA hRep hCut hEta hNormal ell tau hell htau
    hReserve hLb hAb hCutb hEtab hNormalb r hr z hz
  have he : (fun w : X => (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 : V)) =ᶠ[𝓝 z]
      (fun w => (g.eta ν β (w.1,g.inverse ν β w.1 w.2)*
        (Real.sqrt 2*tau*(g.cutoff ν (w.1,g.inverse ν β w.1 w.2)*Real.sqrt (L w (A w))))) •
          g.normal ν (w.1,g.inverse ν β w.1 w.2)) := by
    filter_upwards [(g.chart ν β).open_target.mem_nhds (hSO hz)] with w hw
    simp only [incrementsGlobalPrimaryLocalFree,dif_pos hw,Submodule.coe_smul,
      Submodule.coe_mk,incrementsGlobalPrimaryB,hRep w hw]
  rw [(he.iteratedFDeriv ℝ r).eq_of_nhds]
  exact hb (g.chart ν β).target S (g.chart ν β).open_target hSO L A
    (fun w : X => g.cutoff ν (w.1,g.inverse ν β w.1 w.2))
    (fun w : X => g.eta ν β (w.1,g.inverse ν β w.1 w.2))
    (fun w : X => g.normal ν (w.1,g.inverse ν β w.1 w.2))
    hL hA hCut hEta hNormal ell tau hell htau hReserve hLb hAb hCutb hEtab hNormalb r hr z hz

/-- The SAME original conditional amplitude responds tamely to its tensor input. -/
theorem incrementCanonical_parameterRound2_original_primary_free_difference_jets_uniform_index
    (n : ℕ) (c Bnd : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ (M : Type uCanonicalM) [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [BoundarylessManifold I M], ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β] (F : Ep → M → V)
      (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (ν : Λ) (β : Β) (S : Set X) (hSO : S ⊆ (g.chart ν β).target)
      (L : X → T →L[ℝ] ℝ) (A Abar : X → T)
      (hL : ContDiffOn ℝ ∞ L (g.chart ν β).target)
      (hA : ContDiffOn ℝ ∞ A (g.chart ν β).target)
      (hAbar : ContDiffOn ℝ ∞ Abar (g.chart ν β).target)
      (hRep : ∀ z ∈ (g.chart ν β).target,
        L z (A z) = g.linearArgument ν z.1 (g.inverse ν β z.1 z.2)
          (input z.1 (g.inverse ν β z.1 z.2)))
      (hRepbar : ∀ z ∈ (g.chart ν β).target,
        L z (Abar z) = g.linearArgument ν z.1 (g.inverse ν β z.1 z.2)
          (inputbar z.1 (g.inverse ν β z.1 z.2)))
      (hCut : ContDiffOn ℝ ∞ (fun z : X => g.cutoff ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (hEta : ContDiffOn ℝ ∞ (fun z : X => g.eta ν β (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (hNormal : ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target)
      (ell tau Delta : ℝ) (hell : 0 < ell) (htau : 0 ≤ tau) (hDelta : 0 ≤ Delta)
      (hReserve : ∀ z ∈ S, c ≤ L z (A z) ∧ c ≤ L z (Abar z))
      (hLb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r L z‖ ≤ Bnd)
      (hAb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r A z‖ ≤ Bnd)
      (hAbarb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r Abar z‖ ≤ Bnd)
      (hCutb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.cutoff ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
      (hEtab : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.eta ν β (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
      (hNormalb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => g.normal ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
      (hDiff : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r (fun w => A w-Abar w) z‖ ≤ Delta),
    ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 : V) -
        (incrementsGlobalPrimaryLocalFree F g inputbar tau ν β w.1 w.2 : V)) z‖ ≤ K*tau*Delta := by
  obtain ⟨K,hK,hb⟩ := actual_subordinate_primary_free_difference_jets_uniform n c Bnd hc hBnd
  refine ⟨K,hK,?_⟩
  intro M _ _ _ _
  intro Λ Β _ _ F g input inputbar ν β S hSO L A Abar hL hA hAbar hRep hRepbar hCut hEta hNormal
    ell tau Delta hell htau hDelta hReserve hLb hAb hAbarb hCutb hEtab hNormalb hDiff r hr z hz
  have he : (fun w : X => (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 : V) -
      (incrementsGlobalPrimaryLocalFree F g inputbar tau ν β w.1 w.2 : V)) =ᶠ[𝓝 z]
      (fun w => (g.eta ν β (w.1,g.inverse ν β w.1 w.2)*
        (Real.sqrt 2*tau*(g.cutoff ν (w.1,g.inverse ν β w.1 w.2)*Real.sqrt (L w (A w))))) •
          g.normal ν (w.1,g.inverse ν β w.1 w.2) -
        (g.eta ν β (w.1,g.inverse ν β w.1 w.2)*
          (Real.sqrt 2*tau*(g.cutoff ν (w.1,g.inverse ν β w.1 w.2)*Real.sqrt (L w (Abar w))))) •
            g.normal ν (w.1,g.inverse ν β w.1 w.2)) := by
    filter_upwards [(g.chart ν β).open_target.mem_nhds (hSO hz)] with w hw
    simp only [incrementsGlobalPrimaryLocalFree,dif_pos hw,Submodule.coe_smul,
      Submodule.coe_mk,incrementsGlobalPrimaryB,hRep w hw,hRepbar w hw]
  rw [(he.iteratedFDeriv ℝ r).eq_of_nhds]
  exact hb (g.chart ν β).target S (g.chart ν β).open_target hSO L A Abar
    (fun w : X => g.cutoff ν (w.1,g.inverse ν β w.1 w.2))
    (fun w : X => g.eta ν β (w.1,g.inverse ν β w.1 w.2))
    (fun w : X => g.normal ν (w.1,g.inverse ν β w.1 w.2))
    hL hA hAbar hCut hEta hNormal ell tau Delta hell htau hDelta hReserve hLb hAb hAbarb hCutb hEtab hNormalb hDiff r hr z hz

end GlobalEmbedding.Continuation



#print axioms GlobalEmbedding.Continuation.incrementCanonical_parameterRound2_original_primary_free_jets_uniform_index
#print axioms GlobalEmbedding.Continuation.incrementCanonical_parameterRound2_original_primary_free_difference_jets_uniform_index
