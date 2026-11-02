import GlobalEmbedding.Paper.PlanarProjectiveHopfFlow
import GlobalEmbedding.Paper.PlanarHopfGenerator
import GlobalEmbedding.Paper.PlanarRealRankOneProjector
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The genuine native Hopf generator

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines258–259.
DAG node: `planar-projective-hopf-generator`.
-/

noncomputable section
open Manifold
open Bundle (TotalSpace)
open scoped ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- Apply the actual tangent map of the smooth Hopf action to the time-unit tangent vector.
This construction uses the genuine tangent bundle rather than a supplied vector field. -/
def planarProjectiveHopfTangentLift (C : ℕ) [Fact (0 < C)]
    (z : PlanarRealProjective C) : TangentBundle (planarHopfModel C) (PlanarRealProjective C) :=
  tangentMap (𝓘(ℝ, ℝ).prod (planarHopfModel C)) (planarHopfModel C)
    (fun p : ℝ × PlanarRealProjective C ↦ planarProjectiveHopfFlow p.1 p.2)
    ((equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ (planarHopfModel C) (PlanarRealProjective C)).symm
      (TotalSpace.mk' ℝ 0 (1 : ℝ), TotalSpace.mk'
        (EuclideanSpace ℝ (Fin (2 * C - 1))) z 0))

/-- Genuine native tangent-map smoothness gives a smooth total-space generator lift. -/
theorem planarProjectiveHopfTangentLift_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C) (planarHopfModel C).tangent ∞
      (planarProjectiveHopfTangentLift C) := by
  exact ((planarProjectiveHopfFlow_contMDiff C).contMDiff_tangentMap (by simp)).comp
    (contMDiff_equivTangentBundleProd_symm.comp
      (contMDiff_const.prodMk (Bundle.contMDiff_zeroSection ℝ
        (TangentSpace (planarHopfModel C) : PlanarRealProjective C → Type _))))

/-- Its base point is the original sphere point, by the actual flow-zero identity. -/
theorem planarProjectiveHopfTangentLift_base (C : ℕ) [Fact (0 < C)] (z : PlanarRealProjective C) :
    (planarProjectiveHopfTangentLift C z).proj = z := planarProjectiveHopfFlow_zero z

/-- The actual tangent generator is the fiber component of the genuine tangent lift. -/
def planarProjectiveHopfGenerator {C : ℕ} [Fact (0 < C)] (z : PlanarRealProjective C) :
    TangentSpace (planarHopfModel C) z :=
  cast (congrArg (TangentSpace (planarHopfModel C)) (planarProjectiveHopfTangentLift_base C z))
    (planarProjectiveHopfTangentLift C z).2

/-- The generator has exactly the original smooth total-space lift. -/
theorem planarProjectiveHopfGenerator_totalSpace (C : ℕ) [Fact (0 < C)] (z : PlanarRealProjective C) :
    TotalSpace.mk' (EuclideanSpace ℝ (Fin (2 * C - 1))) z (planarProjectiveHopfGenerator z) =
      planarProjectiveHopfTangentLift C z :=
  TotalSpace.mk_cast (planarProjectiveHopfTangentLift_base C z) _

/-- The actual Hopf generator is a smooth native tangent section. -/
def planarProjectiveHopfGeneratorSection (C : ℕ) [Fact (0 < C)] :
    ContMDiffSection (planarHopfModel C) (EuclideanSpace ℝ (Fin (2 * C - 1))) ∞
      (TangentSpace (planarHopfModel C) : PlanarRealProjective C → Type _) where
  toFun := planarProjectiveHopfGenerator
  contMDiff_toFun := by
    simpa only [planarProjectiveHopfGenerator_totalSpace] using planarProjectiveHopfTangentLift_contMDiff C

/-- The constructed native vector is the genuine orbit mfderiv at time zero. -/
theorem planarProjectiveHopfGenerator_eq_orbit_mfderiv (C : ℕ) [Fact (0 < C)]
    (z : PlanarRealProjective C) :
    planarProjectiveHopfGenerator z =
      cast (congrArg (TangentSpace (planarHopfModel C)) (planarProjectiveHopfFlow_zero z))
        (mfderiv 𝓘(ℝ, ℝ) (planarHopfModel C)
          (fun t : ℝ ↦ planarProjectiveHopfFlow t z) 0 (1 : ℝ)) := by
  have h := mfderiv_comp (I := 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, ℝ).prod (planarHopfModel C)) (I'' := planarHopfModel C)
    (f := fun t : ℝ ↦ (t, z))
    (g := fun p : ℝ × PlanarRealProjective C ↦ planarProjectiveHopfFlow p.1 p.2) (x := 0)
    ((planarProjectiveHopfFlow_contMDiff C).mdifferentiableAt (by simp))
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  rw [mfderiv_prod_left] at h
  unfold planarProjectiveHopfGenerator
  congr 1
  change mfderiv (𝓘(ℝ, ℝ).prod (planarHopfModel C)) (planarHopfModel C)
    (fun p : ℝ × PlanarRealProjective C ↦ planarProjectiveHopfFlow p.1 p.2) (0, z) (1, 0) = _
  exact (congrArg (fun L ↦ L (1 : ℝ)) h).symm


/-- The native generator derivative of every actual smooth vector-valued observable is
exactly the shared actual one-variable orbit derivative, with the same time normalization. -/
theorem planarProjectiveHopfGenerator_mvfderiv {C : ℕ} [Fact (0 < C)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : PlanarRealProjective C → F)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, F) ∞ f) (z : PlanarRealProjective C) :
    mvfderiv (planarHopfModel C) f z (planarProjectiveHopfGenerator z) =
      orbitDeriv planarProjectiveHopfFlow f z := by
  have horbit : MDifferentiableAt 𝓘(ℝ, ℝ) (planarHopfModel C)
      (fun t : ℝ ↦ planarProjectiveHopfFlow t z) 0 :=
    (((planarProjectiveHopfFlow_contMDiff C).comp
      (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp))
  have h := mvfderiv_comp (I := planarHopfModel C) (I' := 𝓘(ℝ, ℝ)) 0
    (hf.mdifferentiableAt (by simp)) horbit
  have he := congrArg (fun T : ℝ →L[ℝ] F ↦ T (1 : ℝ)) h
  rw [mvfderiv_eq_fderiv] at he
  change fderiv ℝ (fun t : ℝ ↦ f (planarProjectiveHopfFlow t z)) 0 (1 : ℝ) =
    mvfderiv (planarHopfModel C) f (planarProjectiveHopfFlow 0 z)
      (mfderiv 𝓘(ℝ, ℝ) (planarHopfModel C)
        (fun t : ℝ ↦ planarProjectiveHopfFlow t z) 0 (1 : ℝ)) at he
  rw [planarProjectiveHopfFlow_zero] at he
  rw [planarProjectiveHopfGenerator_eq_orbit_mfderiv]
  exact he.symm


/-- The actual projective generator is the genuine tangent pushforward of the
actual sphere generator, by differentiating literal flow intertwining. -/
theorem planarProjectiveHopfGenerator_projection {C : ℕ} [Fact (0 < C)]
    (z : PlanarHopfSphere C) :
    mfderiv (planarHopfModel C) (planarHopfModel C) planarAntipodalProjection z
      (planarHopfGenerator z) =
      planarProjectiveHopfGenerator (planarAntipodalProjection z) := by
  have horbit : MDifferentiableAt 𝓘(ℝ, ℝ) (planarHopfModel C)
      (fun t : ℝ ↦ planarHopfFlow t z) 0 :=
    ((planarHopfFlow_contMDiff C).comp
      (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp)
  have h := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := planarHopfModel C)
    (I'' := planarHopfModel C) (x := 0)
    (f := fun t : ℝ ↦ planarHopfFlow t z) (g := planarAntipodalProjection)
    ((planarAntipodalProjection_contMDiff C).mdifferentiableAt (by simp)) horbit
  have he := congrArg (fun T ↦ T (1 : ℝ)) h
  rw [planarHopfGenerator_eq_orbit_mfderiv, planarProjectiveHopfGenerator_eq_orbit_mfderiv]
  change mfderiv (planarHopfModel C) (planarHopfModel C) planarAntipodalProjection z
      (mfderiv 𝓘(ℝ, ℝ) (planarHopfModel C) (fun t : ℝ ↦ planarHopfFlow t z) 0 (1 : ℝ)) =
    mfderiv 𝓘(ℝ, ℝ) (planarHopfModel C)
      (fun t : ℝ ↦ planarProjectiveHopfFlow t (planarAntipodalProjection z)) 0 (1 : ℝ)
  change mfderiv 𝓘(ℝ, ℝ) (planarHopfModel C)
      (fun t : ℝ ↦ planarAntipodalProjection (planarHopfFlow t z)) 0 (1 : ℝ) =
    mfderiv (planarHopfModel C) (planarHopfModel C) planarAntipodalProjection
      (planarHopfFlow 0 z)
      (mfderiv 𝓘(ℝ, ℝ) (planarHopfModel C) (fun t : ℝ ↦ planarHopfFlow t z) 0 (1 : ℝ)) at he
  rw [planarHopfFlow_zero] at he
  have hfun : (fun t : ℝ ↦ planarProjectiveHopfFlow t (planarAntipodalProjection z)) =
      (fun t : ℝ ↦ planarAntipodalProjection (planarHopfFlow t z)) :=
    funext (fun t ↦ planarProjectiveHopfFlow_projection t z)
  rw [hfun]
  exact he.symm

/-- The true smooth covering inverse composed with projection is locally identity,
so the actual tangent projection is injective. -/
theorem planarAntipodalProjection_mfderiv_injective {C : ℕ} [Fact (0 < C)]
    (z : PlanarHopfSphere C) :
    Function.Injective (mfderiv (planarHopfModel C) (planarHopfModel C)
      planarAntipodalProjection z) := by
  let hf := planarAntipodalLocalHomeomorph C
  let L := hf.localInverseAt z
  have hL : MDifferentiableAt (planarHopfModel C) (planarHopfModel C) L
      (planarAntipodalProjection z) :=
    ((planarAntipodalLocalInverse_contMDiffOn z).contMDiffAt
      (L.open_source.mem_nhds hf.apply_self_mem_localInverseAt_source)).mdifferentiableAt (by simp)
  have he : (fun w : PlanarHopfSphere C ↦ L (planarAntipodalProjection w))
      =ᶠ[nhds z] id := by
    filter_upwards [L.open_target.mem_nhds hf.self_mem_localInverseAt_target] with w hw
    change L (planarAntipodalProjection w) = w
    simpa only [L, IsLocalHomeomorph.localInverseAt_symm] using L.right_inv hw
  have hd := he.mfderiv_eq (I := planarHopfModel C) (I' := planarHopfModel C)
  change mfderiv (planarHopfModel C) (planarHopfModel C) (L ∘ planarAntipodalProjection) z =
    mfderiv (planarHopfModel C) (planarHopfModel C) id z at hd
  rw [mfderiv_comp z hL
    ((planarAntipodalProjection_contMDiff C).mdifferentiableAt (by simp)), mfderiv_id] at hd
  intro v w hvw
  have hh := congrArg (mfderiv (planarHopfModel C) (planarHopfModel C) L
    (planarAntipodalProjection z)) hvw
  have hdv := congrArg (fun T ↦ T v) hd
  have hdw := congrArg (fun T ↦ T w) hd
  change mfderiv (planarHopfModel C) (planarHopfModel C) L (planarAntipodalProjection z)
    (mfderiv (planarHopfModel C) (planarHopfModel C) planarAntipodalProjection z v) = v at hdv
  change mfderiv (planarHopfModel C) (planarHopfModel C) L (planarAntipodalProjection z)
    (mfderiv (planarHopfModel C) (planarHopfModel C) planarAntipodalProjection z w) = w at hdw
  exact hdv.symm.trans (hh.trans hdw)

/-- The actual native descended generator is nowhere zero. -/
theorem planarProjectiveHopfGenerator_ne_zero {C : ℕ} [Fact (0 < C)]
    (x : PlanarRealProjective C) : planarProjectiveHopfGenerator x ≠ 0 := by
  obtain ⟨z, rfl⟩ := planarAntipodalProjection_surjective C x
  rw [← planarProjectiveHopfGenerator_projection]
  exact fun h ↦ planarHopfGenerator_ne_zero z
    ((planarAntipodalProjection_mfderiv_injective z) (h.trans (map_zero _).symm))

/-- The actual native derivative of the genuine descended projector along the
actual descended Hopf generator pulls back to its literal sphere formula. -/
theorem planarProjectiveProjector_mvfderiv_apply {C : ℕ} [Fact (0 < C)]
    (z : PlanarHopfSphere C) (w : PlanarHopfAmbient C) :
    mvfderiv (planarHopfModel C) planarProjectiveProjector
      (planarAntipodalProjection z)
      (planarProjectiveHopfGenerator (planarAntipodalProjection z)) w =
      ⟪(z : PlanarHopfAmbient C), w⟫ •
          ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)) +
        ⟪((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)), w⟫ •
          (z : PlanarHopfAmbient C) := by
  have h := mvfderiv_comp (I := planarHopfModel C) (I' := planarHopfModel C) z
    ((planarProjectiveProjector_contMDiff C).mdifferentiableAt (by simp))
    ((planarAntipodalProjection_contMDiff C).mdifferentiableAt (by simp))
  have he := congrArg (fun T ↦ T (planarHopfGenerator z)) h
  change mvfderiv (planarHopfModel C) planarSphereProjector z (planarHopfGenerator z) =
    mvfderiv (planarHopfModel C) planarProjectiveProjector (planarAntipodalProjection z)
      (mfderiv (planarHopfModel C) (planarHopfModel C) planarAntipodalProjection z
        (planarHopfGenerator z)) at he
  rw [planarProjectiveHopfGenerator_projection] at he
  rw [← he]
  exact planarSphereProjector_mvfderiv_apply z w

end GlobalEmbedding.Paper
