import GlobalEmbedding.Paper.HopfCollarProperties
import GlobalEmbedding.Paper.CollarNativeAnalyticHopfAction
import GlobalEmbedding.Paper.FreeHopfOrbitLift
import GlobalEmbedding.Paper.CollarCauchyKovalevskayaJetReduction

/-!
# Actual time and Hopf derivatives of the same native collar

Source: `main.tex`, prop:collar, equations(5.3)–(5.4), lines543–565.
DAG: `collar-hopf-time-differentiation`; sole worker W2.
Use the genuine original orbit lift and the already accepted actual CK mixed
derivative theorem. No commutation or metric identity is assumed.
-/

noncomputable section
open Set WithLp Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- The original factor derivative is the true orbit-coordinate directional
derivative whenever that actual pulled-back observable is differentiable.
Use the EXISTING literal coordinate-line/flow identity and the real chain rule.
This does not require a separately assumed smooth native derivative field. -/
theorem freeHopf_orbit_hasDerivAt_of_differentiable {a : ℕ} (C : Fin a → ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : FreeHopfProduct C → F) (x : FreeHopfProduct C)
    (y : EuclideanSpace ℝ (Fin a))
    (hU : DifferentiableAt ℝ (U ∘ freeHopfOrbitLift C x) y) (i : Fin a) :
    HasDerivAt (fun t : ℝ ↦ U (freeHopfProductFlow C i t (freeHopfOrbitLift C x y)))
      (fderiv ℝ (U ∘ freeHopfOrbitLift C x) y (EuclideanSpace.single i 1)) 0 := by
  have hline : HasDerivAt
      (fun t : ℝ ↦ y + t • EuclideanSpace.single i 1) (EuclideanSpace.single i 1) 0 := by
    convert (hasDerivAt_const (0 : ℝ) y).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i 1)) using 1 <;> simp
    funext t
    rfl
  have hd := hU.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have heq : (fun t : ℝ ↦ (U ∘ freeHopfOrbitLift C x)
      (y + t • EuclideanSpace.single i 1)) =
      (fun t : ℝ ↦ U (freeHopfProductFlow C i t (freeHopfOrbitLift C x y))) := by
    funext t
    rw [Function.comp_apply, freeHopfOrbitLift_coordinate_line]
  change HasDerivAt (fun t ↦ (U ∘ freeHopfOrbitLift C x)
    (y + t • EuclideanSpace.single i 1)) _ 0 at hd
  rw [heq] at hd
  exact hd

/-- The corresponding literal original Hopf derivative value follows by taking
the actual derivative of the curve just identified. -/
theorem freeHopfDeriv_orbit_of_differentiable {a : ℕ} (C : Fin a → ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : FreeHopfProduct C → F) (x : FreeHopfProduct C)
    (y : EuclideanSpace ℝ (Fin a))
    (hU : DifferentiableAt ℝ (U ∘ freeHopfOrbitLift C x) y) (i : Fin a) :
    freeHopfDeriv C i U (freeHopfOrbitLift C x y) =
      fderiv ℝ (U ∘ freeHopfOrbitLift C x) y (EuclideanSpace.single i 1) :=
  (freeHopf_orbit_hasDerivAt_of_differentiable C U x y hU i).deriv

/-- Native joint omega regularity on the original whole collar gives actual
analyticity of its genuine multi-orbit observable in the existing CK coordinates.
The finite output coordinates are the existing continuous linear equivalence;
no alternative Hopf space, flow or norm is introduced. -/
theorem hopfCollar_orbit_analyticAt {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (r0 : ℝ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω G (Ioo (-r0) r0 ×ˢ univ))
    (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (x : FreeHopfProduct C)
    (y : EuclideanSpace ℝ (Fin a)) :
    AnalyticAt ℝ (fun z : CKJoint a ↦
      (EuclideanSpace.equiv (Fin N) ℝ) (G (z.1, freeHopfOrbitLift C x z.2))) (r, y) := by
  have hc : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) 𝓘(ℝ, Fin a → ℝ) ω
      (fun t : EuclideanSpace ℝ (Fin a) ↦ fun i ↦ t i) :=
    contMDiff_pi_module_iff.2 (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).contMDiff)
  have horbit : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) (freeHopfModel C) ω
      (freeHopfOrbitLift C x) :=
    (collarHopfRealAction_omega C).comp (hc.prodMk contMDiff_const)
  have hm : ContMDiff 𝓘(ℝ, CKJoint a) (𝓘(ℝ, ℝ).prod (freeHopfModel C)) ω
      (fun z : CKJoint a ↦ (z.1, freeHopfOrbitLift C x z.2)) :=
    (contDiff_fst.contMDiff : ContMDiff 𝓘(ℝ, CKJoint a) 𝓘(ℝ, ℝ) ω Prod.fst).prodMk
      (horbit.comp (contDiff_snd.contMDiff :
        ContMDiff 𝓘(ℝ, CKJoint a) 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ω Prod.snd))
  have hg := (hG (r, freeHopfOrbitLift C x y) ⟨hr, mem_univ _⟩).contMDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ _⟩)
  have hu := (EuclideanSpace.equiv (Fin N) ℝ).contDiff.contMDiff.contMDiffAt.comp
    (r, y) (hg.comp (r, y) hm.contMDiffAt)
  exact hu.contDiffAt.analyticAt

/-- Actual time differentiation in the genuine orbit coordinates recovers
the literal original G_r. This is the real curve chain rule and the existing
finite coordinate equivalence, rather than an assumed jet correspondence. -/
theorem hopfCollar_time_orbit_coordinates {a N : ℕ} (C : Fin a → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a))
    (hu : AnalyticAt ℝ (fun z : CKJoint a ↦
      (EuclideanSpace.equiv (Fin N) ℝ) (G (z.1, freeHopfOrbitLift C x z.2))) (r, y)) :
    (EuclideanSpace.equiv (Fin N) ℝ) (hopfCollarRDeriv G r (freeHopfOrbitLift C x y)) =
      ckTimeDerivative (fun z : CKJoint a ↦
        (EuclideanSpace.equiv (Fin N) ℝ) (G (z.1, freeHopfOrbitLift C x z.2))) (r, y) := by
  let e := EuclideanSpace.equiv (Fin N) ℝ
  let u := fun z : CKJoint a ↦ e (G (z.1, freeHopfOrbitLift C x z.2))
  have hline : HasDerivAt (fun s : ℝ ↦ (s, y)) (ckTimeDirection : CKJoint a) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r y)
  have hd := hu.differentiableAt.hasFDerivAt.comp_hasDerivAt r hline
  have hb := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r hd
  have hb' : HasDerivAt (fun s : ℝ ↦ G (s, freeHopfOrbitLift C x y))
      (e.symm (ckTimeDerivative u (r, y))) r := by
    simpa only [e, u, ckTimeDerivative, Function.comp_def, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hb
  have he := congrArg e hb'.deriv
  simpa only [e, u, hopfCollarRDeriv, ContinuousLinearEquiv.apply_symm_apply] using he

/-- Actual Hopf differentiation in the same orbit coordinates is the actual
spatial derivative. Differentiate the EXISTING coordinate-line/flow identity;
the same finite target equivalence only records the genuine derivative. -/
theorem hopfCollar_hopf_orbit_coordinates {a N : ℕ} (C : Fin a → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a))
    (hu : AnalyticAt ℝ (fun z : CKJoint a ↦
      (EuclideanSpace.equiv (Fin N) ℝ) (G (z.1, freeHopfOrbitLift C x z.2))) (r, y))
    (i : Fin a) :
    (EuclideanSpace.equiv (Fin N) ℝ)
      (freeHopfDeriv C i (fun z ↦ G (r, z)) (freeHopfOrbitLift C x y)) =
      ckSpatialDerivative (fun z : CKJoint a ↦
        (EuclideanSpace.equiv (Fin N) ℝ) (G (z.1, freeHopfOrbitLift C x z.2))) (r, y) i := by
  let e := EuclideanSpace.equiv (Fin N) ℝ
  let u := fun z : CKJoint a ↦ e (G (z.1, freeHopfOrbitLift C x z.2))
  have hline : HasDerivAt
      (fun t : ℝ ↦ (r, y + t • EuclideanSpace.single i 1)) (ckSpaceDirection i) 0 := by
    convert (hasDerivAt_const (0 : ℝ) r).prodMk
      ((hasDerivAt_const (0 : ℝ) y).add
        ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i 1))) using 1 <;>
      simp [ckSpaceDirection]
  have hd := hu.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hb := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hd
  have hb' : HasDerivAt
      (fun t : ℝ ↦ G (r, freeHopfProductFlow C i t (freeHopfOrbitLift C x y)))
      (e.symm (ckSpatialDerivative u (r, y) i)) 0 := by
    simpa only [e, u, ckSpatialDerivative, Function.comp_def, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply,
      freeHopfOrbitLift_coordinate_line] using hb
  have he := congrArg e hb'.deriv
  simpa only [e, u, freeHopfDeriv, orbitDeriv,
    ContinuousLinearEquiv.apply_symm_apply] using he

/-- The actual G_r has analytic orbit observables on the SAME interval.
Native analytic differentiation supplies the actual time derivative field;
the already proved genuine coordinate identity identifies it locally with G_r. -/
theorem hopfCollarRDeriv_orbit_analyticAt {a N : ℕ} (C : Fin a → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N)) (r0 : ℝ)
    (x : FreeHopfProduct C)
    (ha : ∀ r ∈ Ioo (-r0) r0, ∀ y : EuclideanSpace ℝ (Fin a),
      AnalyticAt ℝ (fun z : CKJoint a ↦
        (EuclideanSpace.equiv (Fin N) ℝ) (G (z.1, freeHopfOrbitLift C x z.2))) (r, y))
    (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (y : EuclideanSpace ℝ (Fin a)) :
    AnalyticAt ℝ (fun z : CKJoint a ↦ (EuclideanSpace.equiv (Fin N) ℝ)
      (hopfCollarRDeriv G z.1 (freeHopfOrbitLift C x z.2))) (r, y) := by
  let u := fun z : CKJoint a ↦
    (EuclideanSpace.equiv (Fin N) ℝ) (G (z.1, freeHopfOrbitLift C x z.2))
  have hu : AnalyticAt ℝ u (r, y) := ha r hr y
  have ht : AnalyticAt ℝ (ckTimeDerivative u) (r, y) :=
    ((ContinuousLinearMap.apply ℝ (CKVal N) (ckTimeDirection : CKJoint a)).analyticAt _).comp
      hu.fderiv
  apply ht.congr
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds
    (show (r, y) ∈ Ioo (-r0) r0 ×ˢ univ from ⟨hr, mem_univ _⟩)] with z hz
  exact (hopfCollar_time_orbit_coordinates C G z.1 x z.2 (ha z.1 hz.1 z.2)).symm

/-- The actual original time and Hopf derivatives commute as a genuine real
HasDerivAt statement. The hypothesis is actual analyticity of the SAME orbit
observable, not a supplied commutation or jet identity. Native joint omega
regularity supplies this hypothesis by hopfCollar_orbit_analyticAt.

Invoke the accepted W6 ckSpatial_time_commute; identify both genuine curve
derivatives by the original coordinate-line/flow identities and target CLE.
This proof does not repeat the generic Schwarz theorem. -/
theorem hopfCollar_time_hopf_hasDerivAt_of_orbits {a N : ℕ} (C : Fin a → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N)) (r0 : ℝ)
    (x : FreeHopfProduct C)
    (ha : ∀ r ∈ Ioo (-r0) r0, ∀ y : EuclideanSpace ℝ (Fin a),
      AnalyticAt ℝ (fun z : CKJoint a ↦
        (EuclideanSpace.equiv (Fin N) ℝ) (G (z.1, freeHopfOrbitLift C x z.2))) (r, y))
    (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (i : Fin a) :
    HasDerivAt (fun s : ℝ ↦ freeHopfDeriv C i (fun z ↦ G (s, z)) x)
      (freeHopfDeriv C i (hopfCollarRDeriv G r) x) r := by
  let e := EuclideanSpace.equiv (Fin N) ℝ
  let u := fun z : CKJoint a ↦ e (G (z.1, freeHopfOrbitLift C x z.2))
  have hu : AnalyticAt ℝ u (r, 0) := ha r hr 0
  have hs : AnalyticAt ℝ (fun z : CKJoint a ↦ ckSpatialDerivative u z i) (r, 0) :=
    ((ContinuousLinearMap.apply ℝ (CKVal N) (ckSpaceDirection i)).analyticAt _).comp hu.fderiv
  have ht : AnalyticAt ℝ (ckTimeDerivative u) (r, 0) :=
    ((ContinuousLinearMap.apply ℝ (CKVal N) (ckTimeDirection : CKJoint a)).analyticAt _).comp
      hu.fderiv
  have hline : HasDerivAt (fun s : ℝ ↦ (s, (0 : CKX a)))
      (ckTimeDirection : CKJoint a) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r (0 : CKX a))
  have hdt := hs.differentiableAt.hasFDerivAt.comp_hasDerivAt r hline
  rw [ckSpatial_time_commute u (r, 0) hu i] at hdt
  have hdtb : HasDerivAt (fun s : ℝ ↦ e.symm (ckSpatialDerivative u (s, 0) i))
      (e.symm (ckMixedDerivative u (r, 0) i)) r := by
    simpa only [ContinuousLinearEquiv.coe_coe, Function.comp_def, ckMixedDerivative] using
      e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r hdt
  have hfirst : (fun s : ℝ ↦ freeHopfDeriv C i (fun z ↦ G (s, z)) x) =ᶠ[𝓝 r]
      (fun s : ℝ ↦ e.symm (ckSpatialDerivative u (s, 0) i)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    have he := hopfCollar_hopf_orbit_coordinates C G s x 0 (ha s hs 0) i
    rw [freeHopfOrbitLift_zero] at he
    calc
      _ = e.symm (e (freeHopfDeriv C i (fun z ↦ G (s, z)) x)) :=
        (e.symm_apply_apply _).symm
      _ = _ := congrArg e.symm he
  have hdtNative := hdtb.congr_of_eventuallyEq hfirst
  have hspace : HasDerivAt
      (fun t : ℝ ↦ (r, t • EuclideanSpace.single i 1)) (ckSpaceDirection i) 0 := by
    convert (hasDerivAt_const (0 : ℝ) r).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ))) using 1 <;>
      simp [ckSpaceDirection]
  have hmt := ht.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hspace (by simp)
  have hmtb : HasDerivAt (fun t : ℝ ↦ e.symm (ckTimeDerivative u
      (r, t • EuclideanSpace.single i 1))) (e.symm (ckMixedDerivative u (r, 0) i)) 0 := by
    simpa only [ContinuousLinearEquiv.coe_coe, Function.comp_def, ckMixedDerivative] using
      e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hmt
  have hsecond : (fun t : ℝ ↦ hopfCollarRDeriv G r (freeHopfProductFlow C i t x)) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ e.symm (ckTimeDerivative u (r, t • EuclideanSpace.single i 1))) := by
    apply Filter.Eventually.of_forall
    intro t
    have he := hopfCollar_time_orbit_coordinates C G r x
      (t • EuclideanSpace.single i 1) (ha r hr _)
    have hflow : freeHopfOrbitLift C x (t • EuclideanSpace.single i 1) =
        freeHopfProductFlow C i t x := by
      simpa only [zero_add, freeHopfOrbitLift_zero] using
        freeHopfOrbitLift_coordinate_line C x 0 i t
    rw [hflow] at he
    calc
      _ = e.symm (e (hopfCollarRDeriv G r (freeHopfProductFlow C i t x))) :=
        (e.symm_apply_apply _).symm
      _ = _ := congrArg e.symm he
  have hmix : freeHopfDeriv C i (hopfCollarRDeriv G r) x =
      e.symm (ckMixedDerivative u (r, 0) i) :=
    (hmtb.congr_of_eventuallyEq hsecond).deriv
  rw [← hmix] at hdtNative
  exact hdtNative

/-- The actual native whole-collar version: no orbit-analyticity or derivative
compatibility is assumed. Native joint omega supplies the genuine observables. -/
theorem hopfCollar_time_hopf_hasDerivAt {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (r0 : ℝ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω G (Ioo (-r0) r0 ×ˢ univ))
    (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (x : FreeHopfProduct C) (i : Fin a) :
    HasDerivAt (fun s : ℝ ↦ freeHopfDeriv C i (fun z ↦ G (s, z)) x)
      (freeHopfDeriv C i (hopfCollarRDeriv G r) x) r :=
  hopfCollar_time_hopf_hasDerivAt_of_orbits C G r0 x
    (fun s hs y ↦ hopfCollar_orbit_analyticAt C r0 G hG s hs x y) r hr i

/-- The actual spatial orbit observable is differentiable in the original
Euclidean target. This only undoes the existing finite coordinate CLE after
restricting the genuine analytic joint observable to a fixed time slice. -/
theorem hopfCollar_slice_orbit_differentiableAt {a N : ℕ} (C : Fin a → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a))
    (hu : AnalyticAt ℝ (fun z : CKJoint a ↦
      (EuclideanSpace.equiv (Fin N) ℝ) (G (z.1, freeHopfOrbitLift C x z.2))) (r, y)) :
    DifferentiableAt ℝ ((fun z ↦ G (r, z)) ∘ freeHopfOrbitLift C x) y := by
  have hs := hu.differentiableAt.comp y
    ((differentiableAt_const r).prodMk differentiableAt_id)
  have hb := (EuclideanSpace.equiv (Fin N) ℝ).symm.differentiableAt.comp y hs
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hb

/-- The actual time curve is differentiable with its literal original G_r.
Undo the existing finite target coordinates after the genuine time-slice chain
rule. The same statement applies to actual G_r using its proved orbit analyticity. -/
theorem hopfCollar_time_hasDerivAt_of_orbit {a N : ℕ} (C : Fin a → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C)
    (hu : AnalyticAt ℝ (fun z : CKJoint a ↦
      (EuclideanSpace.equiv (Fin N) ℝ) (G (z.1, freeHopfOrbitLift C x z.2))) (r, 0)) :
    HasDerivAt (fun s : ℝ ↦ G (s, x)) (hopfCollarRDeriv G r x) r := by
  have hline : DifferentiableAt ℝ (fun s : ℝ ↦ (s, (0 : CKX a))) r :=
    differentiableAt_id.prodMk (differentiableAt_const (0 : CKX a))
  have hs := hu.differentiableAt.comp r hline
  have hb := (EuclideanSpace.equiv (Fin N) ℝ).symm.differentiableAt.comp r hs
  have hb' : DifferentiableAt ℝ (fun s : ℝ ↦ G (s, x)) r := by
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply,
      freeHopfOrbitLift_zero] using hb
  exact hb'.hasDerivAt

end GlobalEmbedding.Paper
