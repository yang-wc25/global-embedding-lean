import GlobalEmbedding.Paper.ManifoldFlatOn
import GlobalEmbedding.Paper.MatrixPlanarSelectorProperties
import GlobalEmbedding.Paper.MatrixScalarBase
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual second Hopf derivatives of fully flat perturbations

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines285–286 and355–366.
The original scalar potential and the actual period-one orbit derivative are used throughout.
-/

noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- Full native chart flatness gives zero full jets after any actual smooth local pullback.
This reverse local-pullback bridge uses ordinary native models, including the actual Hopf atlas. -/
theorem manifold_flat_on_local_pullback_jets
    {P N Q F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    [TopologicalSpace Q] [ChartedSpace N Q] [IsManifold 𝓘(ℝ, N) ∞ Q]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Q → F) (Z : Set Q) (hf : ManifoldFlatOn (I := 𝓘(ℝ, N)) f Z)
    (g : P → Q) (p : P) (hg : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, N) ∞ g p)
    (hp : g p ∈ Z) (n : ℕ) : iteratedFDeriv ℝ n (f ∘ g) p = 0 := by
  let e := chartAt N (g p)
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, N) ∞ Q :=
    IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, N)) (n := ∞) (g p)
  have hs : g p ∈ e.source := mem_chart_source N (g p)
  have ht : e (g p) ∈ e.target := e.map_source hs
  have hj (k : ℕ) : iteratedFDeriv ℝ k (f ∘ e.symm) (e (g p)) = 0 := by
    simpa only [mfld_simps] using hf.2 (g p) hp e he hs k
  have hInv : ContMDiffOn 𝓘(ℝ, N) 𝓘(ℝ, N) ∞ e.symm e.target :=
    contMDiffOn_chart_symm
  have houter : ContDiffAt ℝ ∞ (f ∘ e.symm) (e (g p)) :=
    ((hf.1.comp_contMDiffOn hInv).contDiffOn).contDiffAt (e.open_target.mem_nhds ht)
  have hinner : ContDiffAt ℝ ∞ (fun x ↦ e (g x)) p :=
    ((contMDiffAt_of_mem_maximalAtlas he hs).comp p hg).contDiffAt
  have hlocal : (f ∘ g) =ᶠ[𝓝 p] (f ∘ e.symm) ∘ (fun x ↦ e (g x)) := by
    filter_upwards [hg.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hs)] with x hx
    simp only [Function.comp_apply, e.left_inv hx]
  rw [(hlocal.iteratedFDeriv ℝ n).eq_of_nhds]
  rw [iteratedFDeriv_comp (f := fun x : P ↦ e (g x)) houter hinner (show (n : ℕ∞ω) ≤ ∞ by simp)]
  ext v
  simp only [FormalMultilinearSeries.taylorComp, sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries,
    hj, zero_apply, Finset.sum_const_zero]

variable {C : ℕ} [Fact (0 < C)]

omit [Fact (0 < C)] in
/-- The actual iterated Hopf derivative is the actual second derivative of the same orbit map. -/
theorem planarHopf_second_orbitDeriv_eq (u : PlanarHopfSphere C → ℝ)
    (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow u) z =
      iteratedDeriv 2 (fun t : ℝ ↦ u (planarHopfFlow t z)) 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  change deriv (fun t ↦ orbitDeriv planarHopfFlow u (planarHopfFlow t z)) 0 = _
  congr 1
  funext t
  exact orbitDeriv_flow planarHopfFlow planarHopfFlow_add u t z

/-- Full native flatness gives zero actual second Hopf derivative at every point of the set. -/
theorem planarHopf_flat_second_orbitDeriv (u : PlanarHopfSphere C → ℝ)
    (Z : Set (PlanarHopfSphere C))
    (hu : ManifoldFlatOn (I := planarHopfModel C) u Z)
    (z : PlanarHopfSphere C) (hz : z ∈ Z) :
    orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow u) z = 0 := by
  have hg : ContMDiffAt 𝓘(ℝ, ℝ) (planarHopfModel C) ∞
      (fun t : ℝ ↦ planarHopfFlow t z) 0 :=
    ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).contMDiffAt
  have hj := manifold_flat_on_local_pullback_jets u Z hu
    (fun t : ℝ ↦ planarHopfFlow t z) 0 hg (by simpa only [planarHopfFlow_zero] using hz) 2
  change iteratedFDeriv ℝ 2 (fun t : ℝ ↦ u (planarHopfFlow t z)) 0 = 0 at hj
  rw [planarHopf_second_orbitDeriv_eq, iteratedDeriv_eq_iteratedFDeriv, hj]
  rfl

/-- The literal scalar potential has the actual first orbit derivative inner(f,Xf). -/
theorem matrixScalarPotential_orbitDeriv (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (matrixScalarPotential f) z =
      ⟪f z, orbitDeriv planarHopfFlow f z⟫ := by
  have hd := (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add f hf 0 z).norm_sq.div_const 2
  have he := hd.deriv
  calc
    _ = 2 * ⟪f z, orbitDeriv planarHopfFlow f z⟫ / 2 := by
      simpa only [matrixScalarPotential, orbitDeriv, planarHopfFlow_zero] using he
    _ = _ := by ring

/-- The literal scalar potential has actual second derivative speed squared plus inner(f,X²f). -/
theorem matrixScalarPotential_second_orbitDeriv (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow (matrixScalarPotential f)) z =
      ‖orbitDeriv planarHopfFlow f z‖ ^ 2 +
        ⟪f z, orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow f) z⟫ := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have hfun : orbitDeriv planarHopfFlow (matrixScalarPotential f) =
      fun q ↦ ⟪f q, orbitDeriv planarHopfFlow f q⟫ :=
    funext (matrixScalarPotential_orbitDeriv f hf)
  rw [hfun]
  have hd := (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add f hf 0 z).inner ℝ
      (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
        planarHopfFlow_add _ hv 0 z)
  simpa only [orbitDeriv, planarHopfFlow_zero, real_inner_self_eq_norm_sq, add_comm] using
    hd.deriv

/-- The same actual selector's scalar potential has second Hopf derivative one where κ=0. -/
theorem matrixScalarPotential_second_eq_one (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C)
    (hz : planarOrbitCurvature planarHopfFlow f z = 0) :
    orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow (matrixScalarPotential f)) z = 1 := by
  rw [matrixScalarPotential_second_orbitDeriv f hf.smooth z, hf.unit_speed z,
    hf.acceleration z, hz, zero_smul, inner_zero_right]
  norm_num

/-- Subtracting actual smooth scalar observables subtracts their actual orbit derivatives. -/
theorem planarHopf_orbitDeriv_sub (f g : PlanarHopfSphere C → ℝ)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ g) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (fun q ↦ f q - g q) z =
      orbitDeriv planarHopfFlow f z - orbitDeriv planarHopfFlow g z := by
  have hd := (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add f hf 0 z).fun_sub
      (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
        planarHopfFlow_add g hg 0 z)
  simpa only [orbitDeriv, planarHopfFlow_zero] using hd.deriv

/-- Subtracting actual smooth scalar observables subtracts their actual second orbit derivatives. -/
theorem planarHopf_second_orbitDeriv_sub (f g : PlanarHopfSphere C → ℝ)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ g) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow (fun q ↦ f q - g q)) z =
      orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow f) z -
        orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow g) z := by
  have hfun : orbitDeriv planarHopfFlow (fun q ↦ f q - g q) =
      fun q ↦ orbitDeriv planarHopfFlow f q - orbitDeriv planarHopfFlow g q :=
    funext (planarHopf_orbitDeriv_sub f g hf hg)
  rw [hfun]
  exact planarHopf_orbitDeriv_sub _ _
    (contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf)
    (contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) g hg) z

/-- The original full native flat perturbation condition implies the original actual X²η=1
on κ=0 for the same actual selector. Smoothness of η is derived from the flat difference. -/
theorem planar_flat_second_jet (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (η : PlanarHopfSphere C → ℝ)
    (hflat : ManifoldFlatOn (I := planarHopfModel C)
      (fun z ↦ η z - matrixScalarPotential f z) {z | planarOrbitCurvature planarHopfFlow f z = 0})
    (z : PlanarHopfSphere C) (hz : planarOrbitCurvature planarHopfFlow f z = 0) :
    orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow η) z = 1 := by
  have hφ := matrixScalarPotential_contMDiff f hf.smooth
  have hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η := by
    convert hflat.1.add hφ using 1
    funext q
    exact (sub_add_cancel _ _).symm
  have hh := planarHopf_flat_second_orbitDeriv _ _ hflat z hz
  rw [planarHopf_second_orbitDeriv_sub η (matrixScalarPotential f) hη hφ z,
    matrixScalarPotential_second_eq_one f hf z hz] at hh
  exact sub_eq_zero.mp hh

#print axioms planar_flat_second_jet
#print axioms matrixScalarPotential_second_orbitDeriv
#print axioms matrixScalarPotential_second_eq_one
#print axioms manifold_flat_on_local_pullback_jets
#print axioms planarHopf_flat_second_orbitDeriv

end GlobalEmbedding.Paper
