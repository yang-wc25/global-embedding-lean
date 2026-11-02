import GlobalEmbedding.Paper.FreeHopfOrbitSourceData
import GlobalEmbedding.Paper.BalancedCompactNeighborhoodSmoothBranch
import GlobalEmbedding.Paper.LittlePeriodicCAlphaComplete

/-!
# An actual common strict-small orbit branch on the entire Hopf product

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines403–418 and477–495.
DAG node: `free-hopf-compact-orbit-branch`.
-/

noncomputable section

open Set WithLp
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Original global native sources construct a genuine common-interval orbit fixed branch.

Proof: construct actual little forcing and multiplication maps on the genuine radial
ambient open set. Their forcing vanishes at time zero by equality of actual values.
The actual whole sphere-product inclusion has compact image inside that open set.
Apply the accepted finite-dimensional compact-neighborhood branch theorem to this real
compact set and these actual coefficients. Pull its actual selected branch back through
the native product inclusion and time swap. Every product point is in the same compact
parameter set, so all fixed equations, strict bounds and the O(time) norm estimate hold
on one common interval. No selected solution or desired norm bound is assumed.
Source: the compact-parameter contraction in lem:balanced, lines403–418. -/
theorem freeHopf_compact_orbit_branch {a d N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] {α : ℝ}
    (Q : LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a d 2 α)
    (hQ : ∀ v w, Q v w = Q w v)
    (R : ℝ) (hR : 0 < R)
    (sourceA : ℝ × FreeHopfProduct C →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (sourcef : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) ∞
      sourceA (Metric.ball (0 : ℝ) R ×ˢ univ))
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ sourcef (Metric.ball (0 : ℝ) R ×ˢ univ))
    (hf0 : ∀ x, sourcef (0, x) = 0) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ δ < R ∧
      ∃ f : ℝ × FreeHopfProduct C → LittlePeriodicCAlphaFunction a N 2 α,
      ∃ A : ℝ × FreeHopfProduct C → LittlePeriodicCAlphaFunction a d 2 α →L[ℝ]
          LittlePeriodicCAlphaFunction a N 2 α,
      ∃ v : ℝ × FreeHopfProduct C → LittlePeriodicCAlphaFunction a N 2 α,
        ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
          𝓘(ℝ, LittlePeriodicCAlphaFunction a N 2 α) ∞ v
          (Metric.ball (0 : ℝ) δ ×ˢ univ) ∧
        (∀ x, v (0, x) = 0) ∧
        ∀ (t : ℝ), t ∈ Metric.ball (0 : ℝ) δ → ∀ x : FreeHopfProduct C,
          (∀ y, (f (t, x)).val.toFun y =
            sourcef (t, freeHopfRealAction C (fun i ↦ y i) x)) ∧
          (∀ (u : LittlePeriodicCAlphaFunction a d 2 α) y,
            (A (t, x) u).val.toFun y =
              sourceA (t, freeHopfRealAction C (fun i ↦ y i) x) (u.val.toFun y)) ∧
          v (t, x) = f (t, x) + A (t, x) (Q (v (t, x)) (v (t, x))) ∧
          ‖v (t, x)‖ ≤ L * |t| ∧ ‖(2 : ℝ) • (A (t, x)).comp (Q (v (t, x)))‖ < 1 := by
  let U := (freeHopfAmbientDomain C : Set (FreeHopfAmbientSpace C))
  let K := Set.range (freeHopfAmbientInclusion C)
  obtain ⟨f, A, hfval, hAval, hfs, hAs, _, _⟩ :=
    freeHopfOrbitSource_little_data_exists C (Metric.ball (0 : ℝ) R) Metric.isOpen_ball
      sourceA sourcef hA hf hα0 hα1
  have hfzero : ∀ p ∈ U, f (p, 0) = 0 := by
    intro p hp
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    change (f (p, 0)).val.toFun = (0 : PeriodicCAlphaFunction a N 2 α).toFun
    rw [(periodicCAlpha_pointwise_operations a N 2 α).1]
    funext y
    exact (hfval (p, 0) ⟨hp, by simpa using hR⟩ y).trans
      (freeHopfOrbitSource_zero_time C sourcef hf0 p y)
  obtain ⟨V, hV, hKV, hVU, _, δ, L, hδ, hL, hδR, v, hvs, hvzero, hspec, _⟩ :=
    balanced_compact_neighborhood_smooth_branch Q hQ U K (freeHopfAmbientDomain C).isOpen
      (freeHopfAmbientInclusion_isCompact_range C) (freeHopfAmbientInclusion_range_subset C)
      R hR A f hfs hAs hfzero
  let lift : ℝ × FreeHopfProduct C → FreeHopfAmbientSpace C × ℝ :=
    fun z ↦ (freeHopfAmbientInclusion C z.2, z.1)
  have hlift : ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, FreeHopfAmbientSpace C × ℝ) ∞ lift :=
    ((freeHopfAmbientInclusion_contMDiff C).comp contMDiff_snd).prodMk_space contMDiff_fst
  have hliftmem : Set.MapsTo lift (Metric.ball (0 : ℝ) δ ×ˢ univ)
      (V ×ˢ Metric.ball (0 : ℝ) δ) := by
    intro z hz
    exact ⟨hKV (Set.mem_range_self z.2), hz.1⟩
  refine ⟨δ, L, hδ, hL, hδR, f ∘ lift, A ∘ lift, v ∘ lift,
    hvs.contMDiffOn.comp hlift.contMDiffOn hliftmem, ?_, ?_⟩
  · intro x
    exact hvzero _ (hKV (Set.mem_range_self x))
  · intro t ht x
    have hxV : freeHopfAmbientInclusion C x ∈ V := hKV (Set.mem_range_self x)
    have hxU : freeHopfAmbientInclusion C x ∈ U := hVU (subset_closure hxV)
    have htR : t ∈ Metric.ball (0 : ℝ) R := Metric.ball_subset_ball hδR.le ht
    have hdata := hspec (freeHopfAmbientInclusion C x, t) ⟨hxV, ht⟩
    refine ⟨?_, ?_, hdata.1, hdata.2.1, lt_of_le_of_lt hdata.2.2.1 (by norm_num)⟩
    · intro y
      exact (hfval _ ⟨hxU, htR⟩ y).trans (freeHopfOrbitSource_inclusion C sourcef t x y)
    · intro u y
      exact (hAval _ ⟨hxU, htR⟩ u y).trans
        (congrArg (fun T ↦ T (u.val.toFun y))
          (freeHopfOrbitSource_inclusion C sourceA t x y))

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopf_compact_orbit_branch
