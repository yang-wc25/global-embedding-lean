import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import GlobalEmbedding.Paper.AvoidanceManifoldLocalNull
import GlobalEmbedding.Paper.AvoidanceCountableLocalNull
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Finite-parameter avoidance

Source: `literature/parallelizable-stable-plus-one/main.tex`, Lemma
`lem:avoidance`, lines 935–941. The target is an incidence statement: only the selected
(relevant) zero or incidence set is required to satisfy the rank hypothesis. The parameter set
is open, the source manifold need not be compact or connected, and the derivative condition is
only a lower bound on its real rank.

The maps below are represented by total functions on the ambient product, smooth on the open
parameter domain. This is equivalent to giving a smooth map on `P × Y`: a function on that open
set has a set-theoretic extension to the ambient product, and its derivative at points of `P × Y`
is unchanged because `P × Y` is open.
-/

open Manifold
open MeasureTheory
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- Finite-parameter avoidance for zeros of a smooth map.

Let `P` be open in `ℝ^p`, and let `Y` be a second-countable smooth manifold of dimension `a`.
`R` is any selected set of relevant points in `P × Y` on which `D` vanishes. If the real rank of
the joint derivative of `D` is at least `k > a` at each point of `R`, the parameter projection
of `R` has Lebesgue measure zero. In particular, `R` may be the full zero incidence set, or any
specified subset of it.

Proof (source: `literature/parallelizable-stable-plus-one/main.tex`, proof of Lemma
`lem:avoidance`, lines 940–941). At a relevant zero, the derivative has at least `k` independent
rows, so choose `k` component equations with independent differentials. Their common zero set
is locally a regular level set in the product, hence is parametrized by a smooth graph of
 dimension `p + a - k < p`; the incidence under consideration is contained in this set. On
compact coordinate cubes inside the graph chart, projection to the parameter space is Lipschitz.
The lower-dimensional Lipschitz-image lemma makes each projected cube null, including the
zero-dimensional case. The product `P × Y` is second countable, so a countable collection of
these neighborhoods covers `R`; countable subadditivity gives nullity of its parameter
projection. If there are no relevant zeros the projection is empty. No compactness of `Y`,
connectedness, global rank condition, or full-rank assumption on `D` is used.
-/
theorem finite_parameter_avoidance
    {p a b : ℕ} {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace Y] [ChartedSpace E Y]
    [IsManifold 𝓘(ℝ, E) ∞ Y] [SecondCountableTopology Y]
    (hDim : Module.finrank ℝ E = a)
    (P : Set (Fin p → ℝ)) (hP : IsOpen P)
    (D : (Fin p → ℝ) × Y → Fin b → ℝ)
    (hD : ContMDiffOn
      ((𝓘(ℝ, (Fin p → ℝ))).prod (𝓘(ℝ, E)))
      (𝓘(ℝ, (Fin b → ℝ))) ∞ D (P ×ˢ Set.univ))
    (R : Set ((Fin p → ℝ) × Y))
    (hRelevant : ∀ z ∈ R, z.1 ∈ P ∧ D z = 0)
    {k : ℕ} (hak : a < k)
    (hRank : ∀ z ∈ R,
      Module.finrank ℝ (LinearMap.range
        ((mfderiv
          ((𝓘(ℝ, (Fin p → ℝ))).prod (𝓘(ℝ, E)))
          (𝓘(ℝ, (Fin b → ℝ))) D z).toLinearMap)) ≥ k) :
    volume (Prod.fst '' R) = 0 := by
  let : ChartedSpace ((Fin p → ℝ) × E) ((Fin p → ℝ) × Y) :=
    prodChartedSpace (Fin p → ℝ) (Fin p → ℝ) E Y
  have hU : IsOpen (P ×ˢ (Set.univ : Set Y)) := hP.prod isOpen_univ
  have : IsManifold 𝓘(ℝ, ((Fin p → ℝ) × E)) ∞ ((Fin p → ℝ) × Y) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓘(ℝ, Fin p → ℝ)) (I' := 𝓘(ℝ, E))
      (n := ∞) (Fin p → ℝ) Y
  have hDs : ContMDiffOn 𝓘(ℝ, ((Fin p → ℝ) × E)) 𝓘(ℝ, Fin b → ℝ) ∞ D (P ×ˢ Set.univ) := by
    simpa only [modelWithCornersSelf_prod] using hD
  have hπ : ContMDiffOn 𝓘(ℝ, ((Fin p → ℝ) × E)) 𝓘(ℝ, Fin p → ℝ) ∞
      (Prod.fst : (Fin p → ℝ) × Y → Fin p → ℝ) (P ×ˢ Set.univ) := by
    simpa only [modelWithCornersSelf_prod] using
      (contMDiffOn_fst (I := 𝓘(ℝ, Fin p → ℝ)) (J := 𝓘(ℝ, E))
        (s := P ×ˢ (Set.univ : Set Y)) (n := ∞))
  apply avoidance_image_null_of_locally_null volume R Prod.fst
  intro x hx
  have hxU : x ∈ P ×ˢ (Set.univ : Set Y) := ⟨(hRelevant x hx).1, Set.mem_univ _⟩
  have hrank : Module.finrank ℝ ((Fin p → ℝ) × E) < p + Module.finrank ℝ
      (LinearMap.range (mfderiv 𝓘(ℝ, ((Fin p → ℝ) × E)) 𝓘(ℝ, Fin b → ℝ) D x).toLinearMap) := by
    have hr := hRank x hx
    have hdimA : Module.finrank ℝ ((Fin p → ℝ) × E) = p + a := by
      simp only [Module.finrank_prod, Module.finrank_fin_fun, hDim]
    rw [← modelWithCornersSelf_prod] at hr
    rw [hdimA]
    omega
  obtain ⟨V, hVo, hxV, hVU, hnull⟩ :=
    avoidance_manifold_local_projection_null hU hDs hπ hxU (hRelevant x hx).2 hrank
  refine ⟨V, hVo, hxV, measure_mono_null ?_ hnull⟩
  rintro t ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz.2, (hRelevant z hz.1).2⟩, rfl⟩

/-- Finite-parameter avoidance for incidence with a submanifold given by local smooth defining
equations.

For each point `y` of the target subset `S`, `U y hy` is an open neighborhood and `equation y hy`
is a smooth local defining map to `ℝ^c`: on `U y hy`, its zero set is exactly `S`, and its
differential is surjective at `y`. The rank hypothesis is on the actual joint derivative of the
composite local incidence equation `(equation y hy) ∘ D`, not on a projected-nullity conclusion.

Proof (source: `literature/parallelizable-stable-plus-one/main.tex`, proof of Lemma
`lem:avoidance`, lines 940–941). At a relevant incidence point choose its local defining
 equations. Since their differential is surjective, the local incidence is their zero set after
composition with `D`. The stated rank bound selects `k` independent component equations. The
regular-level graph theorem then puts the incidence locally inside a smooth graph of dimension
`p + a - k < p`. Projection of compact coordinate cubes in this graph is Lipschitz and null by
the lower-dimensional Lipschitz-image lemma. Second countability supplies a countable cover of
all relevant incidence points, so the parameter projection is null. The equations are only
required locally; different defining systems have the same normal differential up to an
invertible linear map and therefore give the same rank condition. No compactness or connectedness
assumption on `Y` is used.
-/
theorem finite_parameter_avoidance_submanifold
    {p a b c : ℕ} {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace Y] [ChartedSpace E Y]
    [IsManifold 𝓘(ℝ, E) ∞ Y] [SecondCountableTopology Y]
    (hDim : Module.finrank ℝ E = a)
    (P : Set (Fin p → ℝ)) (hP : IsOpen P)
    (D : (Fin p → ℝ) × Y → Fin b → ℝ)
    (hD : ContMDiffOn
      ((𝓘(ℝ, (Fin p → ℝ))).prod (𝓘(ℝ, E)))
      (𝓘(ℝ, (Fin b → ℝ))) ∞ D (P ×ˢ Set.univ))
    (S : Set (Fin b → ℝ))
    (U : ∀ y, y ∈ S → Set (Fin b → ℝ))
    (equation : ∀ y, y ∈ S → (Fin b → ℝ) → Fin c → ℝ)
    (hUopen : ∀ y hy, IsOpen (U y hy))
    (hyU : ∀ y hy, y ∈ U y hy)
    (hequation : ∀ y hy,
      ContMDiffOn (𝓘(ℝ, (Fin b → ℝ)))
        (𝓘(ℝ, (Fin c → ℝ))) ∞ (equation y hy) (U y hy))
    (hzero : ∀ y hy z, z ∈ U y hy → (z ∈ S ↔ equation y hy z = 0))
    (hnormal : ∀ y hy, Function.Surjective
      (mfderiv (𝓘(ℝ, (Fin b → ℝ)))
        (𝓘(ℝ, (Fin c → ℝ))) (equation y hy) y))
    (R : Set ((Fin p → ℝ) × Y))
    (hRelevant : ∀ z ∈ R, z.1 ∈ P ∧ D z ∈ S)
    {k : ℕ} (hak : a < k)
    (hRank : ∀ z (hz : z ∈ R),
      Module.finrank ℝ (LinearMap.range
        ((mfderiv
          ((𝓘(ℝ, (Fin p → ℝ))).prod (𝓘(ℝ, E)))
          (𝓘(ℝ, (Fin c → ℝ)))
          (fun w => equation (D z) (hRelevant z hz).2 (D w)) z).toLinearMap)) ≥ k) :
    volume (Prod.fst '' R) = 0 := by
  let : ChartedSpace ((Fin p → ℝ) × E) ((Fin p → ℝ) × Y) :=
    prodChartedSpace (Fin p → ℝ) (Fin p → ℝ) E Y
  have hPopen : IsOpen (P ×ˢ (Set.univ : Set Y)) := hP.prod isOpen_univ
  have : IsManifold 𝓘(ℝ, ((Fin p → ℝ) × E)) ∞ ((Fin p → ℝ) × Y) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓘(ℝ, Fin p → ℝ)) (I' := 𝓘(ℝ, E))
      (n := ∞) (Fin p → ℝ) Y
  have hDs : ContMDiffOn 𝓘(ℝ, ((Fin p → ℝ) × E)) 𝓘(ℝ, Fin b → ℝ) ∞ D (P ×ˢ Set.univ) := by
    simpa only [modelWithCornersSelf_prod] using hD
  have hπ : ContMDiffOn 𝓘(ℝ, ((Fin p → ℝ) × E)) 𝓘(ℝ, Fin p → ℝ) ∞
      (Prod.fst : (Fin p → ℝ) × Y → Fin p → ℝ) (P ×ˢ Set.univ) := by
    simpa only [modelWithCornersSelf_prod] using
      (contMDiffOn_fst (I := 𝓘(ℝ, Fin p → ℝ)) (J := 𝓘(ℝ, E))
        (s := P ×ˢ (Set.univ : Set Y)) (n := ∞))
  apply avoidance_image_null_of_locally_null volume R Prod.fst
  intro x hx
  let e := equation (D x) (hRelevant x hx).2
  have _hnormalAt := hnormal (D x) (hRelevant x hx).2
  let V₀ := (P ×ˢ (Set.univ : Set Y)) ∩ D ⁻¹' U (D x) (hRelevant x hx).2
  have hV₀ : IsOpen V₀ :=
    hDs.continuousOn.isOpen_inter_preimage hPopen (hUopen _ _)
  have hxV₀ : x ∈ V₀ :=
    ⟨⟨(hRelevant x hx).1, Set.mem_univ _⟩, hyU _ _⟩
  have he : ContMDiffOn 𝓘(ℝ, Fin b → ℝ) 𝓘(ℝ, Fin c → ℝ) ∞ e
      (U (D x) (hRelevant x hx).2) := hequation _ _
  have hc : ContMDiffOn 𝓘(ℝ, ((Fin p → ℝ) × E)) 𝓘(ℝ, Fin c → ℝ) ∞ (e ∘ D) V₀ :=
    he.comp (hDs.mono Set.inter_subset_left) (fun z hz ↦ hz.2)
  have hzero' : (e ∘ D) x = 0 :=
    (hzero _ _ _ (hyU _ _)).mp (hRelevant x hx).2
  have hrank : Module.finrank ℝ ((Fin p → ℝ) × E) < p + Module.finrank ℝ
      (LinearMap.range (mfderiv 𝓘(ℝ, ((Fin p → ℝ) × E)) 𝓘(ℝ, Fin c → ℝ) (e ∘ D) x).toLinearMap) := by
    have hr := hRank x hx
    have hdimA : Module.finrank ℝ ((Fin p → ℝ) × E) = p + a := by
      simp only [Module.finrank_prod, Module.finrank_fin_fun, hDim]
    rw [← modelWithCornersSelf_prod] at hr
    change k ≤ Module.finrank ℝ
      (LinearMap.range (mfderiv 𝓘(ℝ, ((Fin p → ℝ) × E)) 𝓘(ℝ, Fin c → ℝ) (e ∘ D) x).toLinearMap) at hr
    rw [hdimA]
    omega
  obtain ⟨V, hVo, hxV, hVV₀, hnull⟩ :=
    avoidance_manifold_local_projection_null hV₀ hc (hπ.mono Set.inter_subset_left)
      hxV₀ hzero' hrank
  refine ⟨V, hVo, hxV, measure_mono_null ?_ hnull⟩
  rintro t ⟨z, hz, rfl⟩
  refine ⟨z, ⟨hz.2, ?_⟩, rfl⟩
  exact (hzero _ _ (D z) (hVV₀ hz.2).2).mp (hRelevant z hz.1).2

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.finite_parameter_avoidance
#print axioms GlobalEmbedding.Paper.finite_parameter_avoidance_submanifold
