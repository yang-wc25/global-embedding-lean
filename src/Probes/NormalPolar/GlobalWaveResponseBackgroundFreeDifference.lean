import Smoothing.ParameterRound2MeanRawProfiles
import Smoothing.ParameterRound2OriginalFreeIndex
import Smoothing.ParameterRound2PrimaryRestriction

/-! The true nonlinear square-root free amplitude of the background has
uniform pairwise jet control from the primitive raw input. Pair-dependent
positive neighborhoods are used only through exact original-field germs.
The source response alone does not include this free term. -/
noncomputable section
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
variable {m N : ℕ}

theorem globalWave_background_free_difference_at_fixed_sample
    (n : ℕ) (reserve Bnd : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) :
    ∃ Ks : ℝ, 0 ≤ Ks ∧ ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β]
      (F : Ep → M → EuclideanSpace ℝ (Fin N))
      (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I:=I) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
      (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (W G : Set (Ep×M)) (hW : IsOpen W) (hG : IsOpen G)
      (primary : Λ → Set (Ep×M)) (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m+1))))
      (O S : Set (Ep×EuclideanSpace ℝ (Fin (m+1))))
      (length j Rsub Lprimary : ℕ) (Mg : ℝ) (T : ℕ → ℝ) (tau ell Delta : ℝ)
      (raw : ParameterRound2GlobalMeanRawProfiles (Tr:=Tr) n length j Rsub Lprimary reserve Bnd Mg T
        F hF (parameterRound2_restrictPrimaryFamily F g G hG) input inputbar G primary e O S tau ell Delta)
      (nu : Λ) (beta : Β) (y : Ep×EuclideanSpace ℝ (Fin (m+1))) (hy : y ∈ S)
      (hyG : (y.1,e.symm y.2) ∈ G)
      (hyActive : (y.1,e.symm y.2) ∈ incrementsGlobalRelativeSupport W
        (fun z => g.eta nu beta z*g.cutoff nu z)),
    ∀ k ≤ n,
      ell^k*‖iteratedFDeriv ℝ k (fun z =>
        (incrementsGlobalPrimaryLocalFree F g input tau nu beta z.1 z.2 : EuclideanSpace ℝ (Fin N))-
        (incrementsGlobalPrimaryLocalFree F g inputbar tau nu beta z.1 z.2 : EuclideanSpace ℝ (Fin N)))
        (g.chart nu beta (y.1,e.symm y.2))‖ ≤ Ks*tau*Delta := by
  obtain ⟨Ks,hKs,hsource⟩ := parameterRound2_original_primary_free_difference_jets_uniform_index
    (I:=I) (M:=M) (Ep:=Ep) (T:=Tr) (m:=m) (N:=N) n reserve Bnd hc hBnd
  refine ⟨Ks,hKs,?_⟩
  intro Λ Β _ _ F hF g input inputbar W G hW hG primary e O S length j Rsub Lprimary Mg T
    tau ell Delta raw nu beta y hy hyG hyActive k hk
  let gG := parameterRound2_restrictPrimaryFamily F g G hG
  let point := (y.1,e.symm y.2)
  let x := g.chart nu beta point
  have hprod : point ∈ incrementsGlobalRelativeSupport G
      (fun z => gG.eta nu beta z*gG.cutoff nu z) := by
    rw [parameterRound2_global_relativeSupport_eq G hG]
    rw [parameterRound2_global_relativeSupport_eq W hW] at hyActive
    exact ⟨hyG,hyActive.2⟩
  have hcut : point ∈ incrementsGlobalRelativeSupport G (gG.cutoff nu) := by
    rw [parameterRound2_global_relativeSupport_eq G hG] at hprod ⊢
    exact ⟨hprod.1,tsupport_mul_subset_right hprod.2⟩
  have hx : x ∈ raw.Sloc nu beta := raw.hmap nu beta ⟨⟨hy,hcut⟩,hprod⟩
  have hxTarget : x ∈ (gG.chart nu beta).target := raw.hSloc nu beta hx
  have hb := hsource F gG input inputbar nu beta (raw.Sloc nu beta) (raw.hSloc nu beta)
    (raw.L nu beta) (raw.A nu beta) (raw.Abar nu beta) (raw.hL nu beta) (raw.hInput nu beta)
    (raw.hInputbar nu beta) (raw.hRep nu beta) (raw.hRepbar nu beta) (raw.hCut nu beta)
    (raw.hEta nu beta) (raw.hNormal nu beta) ell tau Delta
    (raw.htau.trans_le raw.htaul) raw.htau.le raw.hDelta (raw.hReserve nu beta)
    (raw.hLb nu beta) (raw.hInputb nu beta) (raw.hInputbarb nu beta)
    (raw.hCutb nu beta) (raw.hEtab nu beta) (raw.hNormalb nu beta) (raw.hDiff nu beta)
  have heq : (fun z => (incrementsGlobalPrimaryLocalFree F gG input tau nu beta z.1 z.2 : EuclideanSpace ℝ (Fin N))-
      (incrementsGlobalPrimaryLocalFree F gG inputbar tau nu beta z.1 z.2 : EuclideanSpace ℝ (Fin N))) =ᶠ[𝓝 x]
      (fun z => (incrementsGlobalPrimaryLocalFree F g input tau nu beta z.1 z.2 : EuclideanSpace ℝ (Fin N))-
        (incrementsGlobalPrimaryLocalFree F g inputbar tau nu beta z.1 z.2 : EuclideanSpace ℝ (Fin N))) := by
    filter_upwards [(gG.chart nu beta).open_target.mem_nhds hxTarget] with z hz
    exact congrArg₂ Sub.sub
      (congrArg (fun v : normalSpace (I := I) (F z.1) (g.inverse nu beta z.1 z.2) =>
        (v : EuclideanSpace ℝ (Fin N)))
        (parameterRound2_restrictPrimary_localFree F g G hG input tau nu beta z hz))
      (congrArg (fun v : normalSpace (I := I) (F z.1) (g.inverse nu beta z.1 z.2) =>
        (v : EuclideanSpace ℝ (Fin N)))
        (parameterRound2_restrictPrimary_localFree F g G hG inputbar tau nu beta z hz))
  change ell^k*‖iteratedFDeriv ℝ k _ x‖ ≤ _
  rw [← (heq.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hb k hk x hx

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_background_free_difference_at_fixed_sample
