import Initialization.Geometry.AmbientPacking
import Initialization.Geometry.TranslatedCharts
import Initialization.Geometry.CompactChartPreparation
import GlobalEmbedding.Offline.ScaledChartBumps
import GlobalEmbedding.Offline.SquareCutoffNormalization
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual colored cutoffs in finitely many fixed charts

This construction uses Euclidean packing separately in the compact core of
each fixed chart. Colors include the parent-chart index. Consequently no inverse
Lipschitz theorem for an auxiliary embedding, no exponential map, and no
Riemannian volume comparison are needed for the actual square partition.
The original `scaledChartCutoff` is used, with a genuine translated chart.
-/

open Set Metric Manifold IsManifold Topology Function
open scoped ContDiff Manifold ENNReal

noncomputable section
namespace GlobalEmbedding.Initialization

open GlobalEmbedding.Offline

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

/-- Produce the same actual square-normalized family in translated fixed charts.
All input chart data are independent of K. Its palette has `m*(30^n+2)+2`
colors, also in the empty-source case. The support is in the actual parent
chart and the actual radius-ρ/(4K) coordinate ball about the chosen net center. -/
theorem exists_fixedChart_colored_cutoffs_with_nets
    {m : ℕ} (e : Fin m → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (r : Fin m → ℝ)
    (he : ∀ i, e i ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (hr : ∀ i, 0 < r i)
    (hbuffer : ∀ i, closedBall (a i) (4 * r i) ⊆ (e i).target)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source ∧ e i x ∈ ball (a i) (r i))
    {ρ K : ℝ} (hρ : 0 < ρ) (hρr : ∀ i, ρ ≤ r i) (hK : 1 ≤ K) :
    ∃ (N : ℕ) (parent : Fin N → Fin m)
      (p : Fin N → EuclideanSpace ℝ (Fin n))
      (color : Fin N → Fin (m * (30 ^ n + 2) + 2)) (χ : Fin N → M → ℝ),
      (∀ i, p i ∈ closedBall (a (parent i)) (r (parent i))) ∧
      (∀ i j, i ≠ j → parent i = parent j →
        ENNReal.ofReal (ρ / (10 * K)) ≤ edist (p i) (p j)) ∧
      (∀ x : M, ∃ i, x ∈ (e (parent i)).source ∧
        dist (e (parent i) x) (p i) < ρ / (10 * K)) ∧
      (∀ i, χ i = squareNormalizedCutoff
        (fun j ↦ scaledChartCutoff ρ K (translatedChart (e (parent j)) (p j))) i) ∧
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ (χ i)) ∧
      (∀ x, ∑ i, χ i x ^ 2 = 1) ∧
      (∀ i, tsupport (χ i) ⊆ (e (parent i)).source ∩
        (e (parent i)) ⁻¹' closedBall (p i) (ρ / (4 * K))) ∧
      ∀ i j, i ≠ j → color i = color j → Disjoint (tsupport (χ i)) (tsupport (χ j)) := by
  classical
  have hnets (i : Fin m) := exists_compact_euclidean_colored_net
    (isCompact_closedBall (a i) (r i)) hρ hK
  choose P hPcore hPfin hPsep hPcover hPcolor using hnets
  letI (i : Fin m) : Fintype (P i) := (hPfin i).fintype
  let J := (i : Fin m) × P i
  let c (i : Fin m) := Classical.choice (hPcolor i)
  let chart (v : J) := translatedChart (e v.1) (v.2 : EuclideanSpace ℝ (Fin n))
  let b (v : J) : M → ℝ := scaledChartCutoff ρ K (chart v)
  let χ : J → M → ℝ := squareNormalizedCutoff b
  let color : J → Fin (m * (30 ^ n + 2) + 2) := fun v ↦
    (finProdFinEquiv (v.1, c v.1 v.2)).castAdd 2
  have hfamilycover (x : M) : ∃ v : J, x ∈ (e v.1).source ∧
      dist (e v.1 x) (v.2 : EuclideanSpace ℝ (Fin n)) < ρ / (10 * K) := by
    obtain ⟨i, hxi, hxa⟩ := hcover x
    obtain ⟨p, hp, hxp⟩ := hPcover i (e i x) (ball_subset_closedBall hxa)
    refine ⟨⟨i, p, hp⟩, hxi, ?_⟩
    simpa only [← Metric.mem_eball, Metric.eball_ofReal, Metric.mem_ball] using hxp
  have hfamilysep (v w : J) (hvw : v ≠ w) (hparent : v.1 = w.1) :
      ENNReal.ofReal (ρ / (10 * K)) ≤
        edist (v.2 : EuclideanSpace ℝ (Fin n)) (w.2 : EuclideanSpace ℝ (Fin n)) := by
    cases v with
    | mk i p =>
      cases w with
      | mk j q =>
        dsimp only at hparent
        cases hparent
        apply hPsep i p.property q.property
        intro hpq
        apply hvw
        exact congrArg (fun z : P i ↦ (⟨i, z⟩ : J)) (Subtype.ext hpq)
  have hchart (v : J) : chart v ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M :=
    translatedChart_mem_maximalAtlas (e v.1) (he v.1) v.2
  have hchartbuffer (v : J) : closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆ (chart v).target :=
    translatedChart_closedBall_buffer (e v.1) (hr v.1) (hρr v.1)
      (hPcore v.1 v.2.property) (hbuffer v.1)
  have hb (v : J) : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ (b v) :=
    scaledChartCutoff_contMDiff ρ K hρ hK (chart v) (hchart v) (hchartbuffer v)
  have hpositive (x : M) : 1 ≤ squareCutoffSum b x := by
    apply one_le_squareCutoffSum_of_plateau b x
    obtain ⟨i, hxi, hxa⟩ := hcover x
    obtain ⟨p, hp, hxp⟩ := hPcover i (e i x) (ball_subset_closedBall hxa)
    refine ⟨⟨i, p, hp⟩, ?_⟩
    apply scaledChartCutoff_one ρ K hρ hK (chart ⟨i, p, hp⟩)
    refine ⟨hxi, ?_⟩
    have hxpd : dist (e i x) p < ρ / (10 * K) := by
      simpa only [← Metric.mem_eball, Metric.eball_ofReal, Metric.mem_ball] using hxp
    simpa only [Set.mem_preimage, chart, translatedChart_apply, Metric.mem_closedBall,
      dist_zero_right, dist_eq_norm, sub_zero] using hxpd.le
  have hsmooth (v : J) : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ (χ v) :=
    squareNormalizedCutoff_contMDiff b hb hpositive v
  have hsquares (x : M) : ∑ v : J, χ v x ^ 2 = 1 :=
    squareNormalizedCutoff_sum_sq b x (zero_lt_one.trans_le (hpositive x))
  have hsupp (v : J) : tsupport (χ v) ⊆
      (e v.1).source ∩ (e v.1) ⁻¹' closedBall (v.2 : EuclideanSpace ℝ (Fin n))
        (ρ / (4 * K)) := by
    intro x hx
    have hraw := squareNormalizedCutoff_tsupport_subset b v hx
    have hsmall := (scaledChartCutoff_support_buffers ρ K hρ hK (chart v)
      (hchartbuffer v)).2.2.2 hraw
    refine ⟨hsmall.1, ?_⟩
    have hdist : dist (e v.1 x) (v.2 : EuclideanSpace ℝ (Fin n)) < ρ / (4 * K) := by
      simpa only [chart, translatedChart_apply, Set.mem_preimage, Metric.mem_ball,
        dist_zero_right, dist_eq_norm, sub_zero] using hsmall.2
    exact hdist.le
  have hdisjoint (v w : J) (hvw : v ≠ w) (hc : color v = color w) :
      Disjoint (tsupport (χ v)) (tsupport (χ w)) := by
    have hpair : (v.1, c v.1 v.2) = (w.1, c w.1 w.2) :=
      finProdFinEquiv.injective (Fin.castAdd_injective _ 2 hc)
    cases v with
    | mk i p =>
      cases w with
      | mk j q =>
        have hij : i = j := congrArg Prod.fst hpair
        cases hij
        have hpq : p ≠ q := by
          intro h
          subst q
          exact hvw rfl
        have hcolors : c i p = c i q := congrArg Prod.snd hpair
        apply Set.disjoint_left.mpr
        intro x hxp hxq
        have hi := (hsupp ⟨i, p⟩ hxp).2
        have hj := (hsupp ⟨i, q⟩ hxq).2
        have hKpos : 0 < K := zero_lt_one.trans_le hK
        have hi' : e i x ∈ closedEBall (p : EuclideanSpace ℝ (Fin n))
            (ENNReal.ofReal (ρ / (4 * K))) := by
          rw [Metric.closedEBall_ofReal (by positivity)]; exact hi
        have hj' : e i x ∈ closedEBall (q : EuclideanSpace ℝ (Fin n))
            (ENNReal.ofReal (ρ / (4 * K))) := by
          rw [Metric.closedEBall_ofReal (by positivity)]; exact hj
        exact ((c i).valid ⟨hpq, e i x, hi', hj'⟩) hcolors
  let enum : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, (fun i ↦ (enum i).1),
    (fun i ↦ ((enum i).2 : EuclideanSpace ℝ (Fin n))),
    color ∘ enum, χ ∘ enum, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hPcore (enum i).1 (enum i).2.property
  · intro i j hij hparent
    exact hfamilysep (enum i) (enum j) (fun h ↦ hij (enum.injective h)) hparent
  · intro x
    obtain ⟨v, hvs, hvp⟩ := hfamilycover x
    refine ⟨enum.symm v, ?_, ?_⟩
    · simpa only [Equiv.apply_symm_apply] using hvs
    · change dist (e (enum (enum.symm v)).1 x)
        ((enum (enum.symm v)).2 : EuclideanSpace ℝ (Fin n)) < _
      rw [Equiv.apply_symm_apply]
      exact hvp
  · intro i
    funext x
    change b (enum i) x * reciprocalSquareRoot (squareCutoffSum b x) = _
    unfold squareNormalizedCutoff
    congr 1
    congr 1
    exact (enum.sum_comp (fun j ↦ b j x ^ 2)).symm
  · exact fun i ↦ hsmooth (enum i)
  · intro x
    exact (enum.sum_comp (fun j ↦ χ j x ^ 2)).trans (hsquares x)
  · exact fun i ↦ hsupp (enum i)
  · intro i j hij hc
    exact hdisjoint (enum i) (enum j) (fun h ↦ hij (enum.injective h)) hc

/-- The direct cutoff-facing interface, preserving the original statement. -/
theorem exists_fixedChart_colored_cutoffs
    {m : ℕ} (e : Fin m → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (r : Fin m → ℝ)
    (he : ∀ i, e i ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (hr : ∀ i, 0 < r i)
    (hbuffer : ∀ i, closedBall (a i) (4 * r i) ⊆ (e i).target)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source ∧ e i x ∈ ball (a i) (r i))
    {ρ K : ℝ} (hρ : 0 < ρ) (hρr : ∀ i, ρ ≤ r i) (hK : 1 ≤ K) :
    ∃ (N : ℕ) (parent : Fin N → Fin m)
      (p : Fin N → EuclideanSpace ℝ (Fin n))
      (color : Fin N → Fin (m * (30 ^ n + 2) + 2)) (χ : Fin N → M → ℝ),
      (∀ i, p i ∈ closedBall (a (parent i)) (r (parent i))) ∧
      (∀ i, χ i = squareNormalizedCutoff
        (fun j ↦ scaledChartCutoff ρ K (translatedChart (e (parent j)) (p j))) i) ∧
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ (χ i)) ∧
      (∀ x, ∑ i, χ i x ^ 2 = 1) ∧
      (∀ i, tsupport (χ i) ⊆ (e (parent i)).source ∩
        (e (parent i)) ⁻¹' closedBall (p i) (ρ / (4 * K))) ∧
      ∀ i j, i ≠ j → color i = color j → Disjoint (tsupport (χ i)) (tsupport (χ j)) := by
  obtain ⟨N, parent, p, color, χ, hcore, _hsep, _hnet, hχ, hsmooth, hsquares, hsupp,
    hdisjoint⟩ := exists_fixedChart_colored_cutoffs_with_nets e a r he hr hbuffer hcover hρ hρr hK
  exact ⟨N, parent, p, color, χ, hcore, hχ, hsmooth, hsquares, hsupp, hdisjoint⟩

end GlobalEmbedding.Initialization
