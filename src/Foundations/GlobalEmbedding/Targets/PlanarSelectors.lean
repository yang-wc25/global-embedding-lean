import GlobalEmbedding.Paper.FramedDistribution
import GlobalEmbedding.Paper.PlanarHopfFlow
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import GlobalEmbedding.Paper.FramedDistributionPartialImmersion
import GlobalEmbedding.Paper.PlanarEquivariantInitialExistence
import GlobalEmbedding.Paper.PlanarHopfFourierReflection
import GlobalEmbedding.Paper.PlanarOrbitReparametrization
import GlobalEmbedding.Paper.PlanarHopfCurvature
import GlobalEmbedding.Paper.PlanarUnitFreeCurve

/-!
# Partial immersions and whole-sphere planar selectors

Source: `literature/parallelizable-stable-plus-one/main.tex`, Lemma `lem:planar`,
lines 245–266. These three declarations represent all parts of that one original target.
The source spheres, period-one Hopf action, orbit derivatives, averages and Euclidean norms
are actual native objects. The declarations are stage-two statement drafts, not proved results.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- A framed rank-b distribution on an ordinary closed smooth manifold has a genuine
partial immersion into dimension b+1.

Proof plan: for b=0 use a constant map. Otherwise extend the framed-coordinate covectors
smoothly to the tangent bundle and use formal value zero and formal derivative sending the
frame to the first b coordinates. The relation requiring injectivity on the distribution is
open. In each principal slice fixing a hyperplane that contains the distribution the slice is
empty or full. Otherwise the forbidden free derivative values form an affine subspace of
dimension b-1 in dimension b+1; its complement is ample by codimension two. The actual global
open-ample maps h-principle yields a genuine smooth holonomic map. Its derivative restricted
to the actual frame span is injective at each point. Empty sources and b=0 are included.
Source: original `lem:planar`, first assertion and first proof paragraph, lines 245–258.
DAG: `lem-planar`, first declaration. -/
theorem framed_distribution_partial_immersion
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {b : ℕ} («D» : FramedDistribution I (M := M) b) :
    ∃ F : M → EuclideanSpace ℝ (Fin (b + 1)),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (b + 1))) ∞ F ∧
      ∀ x : M, Function.Injective
        (fun v : FramedDistribution.fiber I «D» x ↦
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (b + 1))) F x v.1) := by
  exact framed_distribution_partial_immersion_exists I «D»

/-- One whole-sphere planar map has all the original unit-speed, reflection, signed-area,
orbit analyticity and two-sign curvature properties simultaneously.

Proof plan: on the actual real-projective antipodal quotient, use its smooth rank-one projector
P=zzᵀ and descended nonvanishing Hopf field X. For an ordinary map (a,w) to R⊕R^(2C), impose
the open relation (da(X),P dw(X)+P(dP(X))w)≠0. In each nontrivial principal slice the actual
two-coordinate derivative symbol is onto R², so the forbidden affine fiber has codimension
two; the other slices are full or empty. The formal zero value with derivative β⊗e₁, β(X)=1,
is a genuine formal solution. The actual maps h-principle and the lift
g(z)=(a([z]),inner(w([z]),z)) construct a smooth reflection-equivariant map with Xg nowhere
zero. Finite Fourier approximation along the actual action preserves reflection and nonzero
derivative and makes every orbit profile analytic. Put a=|Xg|, L=average(a),
h=integral t(a/L-1)(R_t z)dt. The genuine orbit shift Φ(z)=R_(h(z))z has positive derivative
a/L and a global smooth inverse. The actual f=(g∘Φ⁻¹)/L has unit X-speed and preserves the
reflection and orbit analyticity. The signed-area integrand is odd under the half-period,
so its actual period integral is zero. For v=Xf, differentiating its unit norm gives Xv⊥v;
κ=inner(J₂v,Xv) is smooth and gives Xv=κJ₂v. Reflection makes κ antipodal-odd. If κ were zero
on a whole orbit, v would be a constant unit vector and the periodic fundamental theorem of
calculus would give v=0. Thus κ is nonzero somewhere on every orbit, and the antipodal point
gives the opposite sign. No global angle lift is required for this unchanged conclusion.
Source: original `lem:planar`, lines 245–265; reflection curvature proof reviewed by root in
`coord/next-target-readiness/ROOT-DECISION.md`. DAG: `lem-planar`, second declaration. -/
theorem planar_hopf_selector (C : ℕ) (hC : 2 ≤ C) :
    letI : Fact (0 < C) := ⟨by omega⟩
    ∃ f : PlanarHopfSphere C → Planar, ∃ κ : PlanarHopfSphere C → ℝ,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f ∧
      (∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1) ∧
      (∀ z, f (-z) = planarReflection (f z)) ∧
      (∀ z, orbitAverage planarHopfFlow
        (fun w ↦ f w 0 * orbitDeriv planarHopfFlow f w 1 -
          f w 1 * orbitDeriv planarHopfFlow f w 0) z = 0) ∧
      (∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) Set.univ) ∧
      ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ ∧
      (∀ z, orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow f) z =
        κ z • planarQuarterTurn (orbitDeriv planarHopfFlow f z)) ∧
      (∀ z, ∃ t s : ℝ, κ (planarHopfFlow t z) < 0 ∧ 0 < κ (planarHopfFlow s z)) := by
  let _ : Fact (0 < C) := ⟨by omega⟩
  obtain ⟨g, hg, hgrefl, hgn⟩ := planar_equivariant_initial_map C hC
  obtain ⟨p, hp, hprefl, hpn, hpana, _, _⟩ :=
    planar_hopf_fourier_reflection C g hg hgrefl hgn 1 zero_lt_one
  have hhalf (z : PlanarHopfSphere C) :
      p (planarHopfFlow (1 / 2 : ℝ) z) = planarReflection (p z) := by
    rw [planarHopfFlow_half]
    exact hprefl z
  obtain ⟨f, hf, hunit, hrefhalf, hana, harea⟩ :=
    planar_orbit_unit_reflected_analytic planarHopfFlow planarHopfFlow_zero
      planarHopfFlow_add planarHopfFlow_one (planarHopfFlow_contMDiff C) p hp hpn hhalf hpana
  have href (z : PlanarHopfSphere C) : f (-z) = planarReflection (f z) := by
    simpa only [planarHopfFlow_half] using hrefhalf z
  obtain ⟨κ, hκ, hacc, hsigns, _⟩ := planar_hopf_curvature f hf hunit href
  exact ⟨f, κ, hf, hunit, href, harea, hana, hκ, hacc, hsigns⟩

/-- A single genuine unit-speed free space curve on the whole Hopf sphere has a global
smooth unit binormal, for every original C≥2.

Proof plan: use the actual planar selector f and set q=(f,|f|²/2). Writing v=Xf, its actual
first two orbit derivatives are (v,inner(f,v)) and (Xv,1+inner(f,Xv)). If Xv≠0 their planar
parts are independent because Xv⊥v and |v|=1. If Xv=0, the last coordinate of the second
derivative is one and its planar part is zero, so independence still holds. Apply the genuine
positive-speed orbit reparametrization to q, including its positive orbit-constant normalization.
The first and second derivatives transform by u↦λu, w↦λ²w+μu with λ≠0; hence independence
persists on the whole sphere and the resulting c has unit X-speed. The actual normalized cross
product of Xc and X²c is smooth, has Euclidean norm one, and is orthogonal to both derivatives.
This constructs the global binormal rather than assuming a trivial complement.
Source: original `lem:planar`, final assertion and final proof paragraph, lines 253–266.
DAG: `lem-planar`, third declaration. -/
theorem planar_hopf_free_curve (C : ℕ) (hC : 2 ≤ C) :
    letI : Fact (0 < C) := ⟨by omega⟩
    ∃ c : PlanarHopfSphere C → SpaceCurve, ∃ ν : PlanarHopfSphere C → SpaceCurve,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, SpaceCurve) ∞ c ∧
      ContMDiff (planarHopfModel C) 𝓘(ℝ, SpaceCurve) ∞ ν ∧
      (∀ z, ‖orbitDeriv planarHopfFlow c z‖ = 1) ∧
      (∀ z, LinearIndependent ℝ
        ![orbitDeriv planarHopfFlow c z,
          orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow c) z]) ∧
      (∀ z, ‖ν z‖ = 1) ∧
      (∀ z, ⟪ν z, orbitDeriv planarHopfFlow c z⟫ = 0) ∧
      (∀ z, ⟪ν z, orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow c) z⟫ = 0) := by
  let _ : Fact (0 < C) := ⟨by omega⟩
  obtain ⟨f, _, hf, hunit, _⟩ := planar_hopf_selector C hC
  exact unit_free_hopf_curve_of_unit_planar f hf hunit

#print axioms framed_distribution_partial_immersion
#print axioms planar_hopf_selector
#print axioms planar_hopf_free_curve

end GlobalEmbedding.Paper
