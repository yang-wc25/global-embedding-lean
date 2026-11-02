import GlobalEmbedding.Paper.FreeHopfProductRetraction
import GlobalEmbedding.Paper.FreeHopfProductAction
import GlobalEmbedding.Paper.BalancedSourceLittleDataExistence

/-!
# Actual periodic orbit sources with genuine finite ambient parameters

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines403–418 and477–495.
DAG node: `free-hopf-orbit-source-data`.
-/

noncomputable section

open Set WithLp
open scoped Manifold ContDiff Topology

namespace GlobalEmbedding.Paper

/-- Actual orbit data over the genuine radial neighborhood. The value outside this open
domain is zero and is never used as smooth source data. No extension hypothesis is assumed. -/
def freeHopfOrbitSource {a : ℕ} (C : Fin a → ℕ) {V : Type*} [Zero V]
    (F : ℝ × FreeHopfProduct C → V) (p : FreeHopfAmbientSpace C × ℝ)
    (y : EuclideanSpace ℝ (Fin a)) : V := by
  classical
  exact if h : p.1 ∈ freeHopfAmbientDomain C then
    F (p.2, freeHopfRealAction C (fun i ↦ y i) (freeHopfRadialRetraction C ⟨p.1, h⟩))
  else 0

/-- At actual product parameters the new sources are exactly the original orbit sources. -/
theorem freeHopfOrbitSource_inclusion {a : ℕ} (C : Fin a → ℕ) {V : Type*} [Zero V]
    (F : ℝ × FreeHopfProduct C → V) (t : ℝ) (x : FreeHopfProduct C)
    (y : EuclideanSpace ℝ (Fin a)) :
    freeHopfOrbitSource C F (freeHopfAmbientInclusion C x, t) y =
      F (t, freeHopfRealAction C (fun i ↦ y i) x) := by
  simp [freeHopfOrbitSource, freeHopfAmbientInclusion_mem, freeHopfRadialRetraction_inclusion]

/-- The actual orbit source is genuinely smooth on its original radial/time domain.

Proof: on the true open ambient domain the factor projection into the radial open subtype
is native smooth, so the actual radial retraction and genuine real Hopf action give a
native smooth input map. Compose the original native smooth source on its open time
domain. Its actual zero extension restricts to that exact map, and open-subtype smoothness
transfers back to the original finite ambient variables. No regularity outside the genuine
domain is asserted. Source: actual smooth compact parameters in lem:balanced, lines403–418. -/
theorem freeHopfOrbitSource_contDiffOn {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (J : Set ℝ) (hJ : IsOpen J) (F : ℝ × FreeHopfProduct C → V)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, V) ∞ F (J ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (freeHopfOrbitSource C F))
      (((freeHopfAmbientDomain C : Set (FreeHopfAmbientSpace C)) ×ˢ J) ×ˢ univ) := by
  let A := FreeHopfAmbientSpace C
  let T := EuclideanSpace ℝ (Fin a)
  let W : TopologicalSpace.Opens ((A × ℝ) × T) :=
    ⟨{z | z.1.1 ∈ freeHopfAmbientDomain C},
      (freeHopfAmbientDomain C).isOpen.preimage (continuous_fst.comp continuous_fst)⟩
  let radialPoint : W → freeHopfAmbientDomain C := fun z ↦ ⟨z.val.1.1, z.property⟩
  have hraw : ContMDiff 𝓘(ℝ, (A × ℝ) × T) 𝓘(ℝ, A) ∞
      (fun z : W ↦ z.val.1.1) :=
    (show ContDiff ℝ ∞ (fun z : (A × ℝ) × T ↦ z.1.1) from
      contDiff_fst.fst).contMDiff.comp contMDiff_subtype_val
  have hradialPoint : ContMDiff 𝓘(ℝ, (A × ℝ) × T) 𝓘(ℝ, A) ∞ radialPoint :=
    (ContMDiff.subtypeVal_comp_iff (freeHopfAmbientDomain C) radialPoint).mp hraw
  have hradial := (freeHopfRadialRetraction_contMDiff C).comp hradialPoint
  have ht : ContMDiff 𝓘(ℝ, (A × ℝ) × T) 𝓘(ℝ, ℝ) ∞
      (fun z : W ↦ z.val.1.2) :=
    (show ContDiff ℝ ∞ (fun z : (A × ℝ) × T ↦ z.1.2) from
      contDiff_fst.snd).contMDiff.comp contMDiff_subtype_val
  have hy : ContMDiff 𝓘(ℝ, (A × ℝ) × T) 𝓘(ℝ, T) ∞
      (fun z : W ↦ z.val.2) :=
    (contDiff_snd : ContDiff ℝ ∞ (fun z : (A × ℝ) × T ↦ z.2)).contMDiff.comp
      contMDiff_subtype_val
  have hcoords : ContMDiff 𝓘(ℝ, T) 𝓘(ℝ, Fin a → ℝ) ∞
      (fun y : T ↦ fun i ↦ y i) :=
    contMDiff_pi_module_iff.2 (fun i ↦
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin a) i).contMDiff)
  have horbit := (freeHopfRealAction_contMDiff C).comp
    ((hcoords.comp hy).prodMk hradial)
  have hinput := ht.prodMk horbit
  intro z hz
  let w : W := ⟨z, hz.1.1⟩
  have hmem : (z.1.2, freeHopfRealAction C (fun i ↦ z.2 i)
      (freeHopfRadialRetraction C ⟨z.1.1, hz.1.1⟩)) ∈ J ×ˢ univ := ⟨hz.1.2, mem_univ _⟩
  have hlocal := (hF.contMDiffAt ((hJ.prod isOpen_univ).mem_nhds hmem)).comp w
    (hinput w)
  have he : (fun v : W ↦ freeHopfOrbitSource C F v.val.1 v.val.2) =
      (fun v : W ↦ F (v.val.1.2, freeHopfRealAction C (fun i ↦ v.val.2 i)
        (freeHopfRadialRetraction C (radialPoint v)))) := by
    funext v
    unfold freeHopfOrbitSource
    split_ifs with hv
    · rfl
    · exact False.elim (hv v.property)
  have hr : ContMDiffAt 𝓘(ℝ, (A × ℝ) × T) 𝓘(ℝ, V) ∞
      (fun v : W ↦ freeHopfOrbitSource C F v.val.1 v.val.2) w := by
    rw [he]
    exact hlocal
  have hAt : ContMDiffAt 𝓘(ℝ, (A × ℝ) × T) 𝓘(ℝ, V) ∞
      (Function.uncurry (freeHopfOrbitSource C F)) z :=
    (contMDiffAt_subtype_iff (I := 𝓘(ℝ, (A × ℝ) × T)) (I' := 𝓘(ℝ, V))
      (U := W) (f := Function.uncurry (freeHopfOrbitSource C F)) (x := w)).mp hr
  exact hAt.contDiffAt.contDiffWithinAt

/-- Genuine integer shifts leave the original period-one multi-action unchanged. -/
theorem freeHopfRealAction_integer_periodic {a : ℕ} (C : Fin a → ℕ)
    (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ) :
    freeHopfRealAction C (fun i ↦ (y + toLp 2 (fun j ↦ (m j : ℝ))) i) x =
      freeHopfRealAction C (fun i ↦ y i) x := by
  rw [← freeHopfTorusAction_real, ← freeHopfTorusAction_real]
  congr 1
  apply PiLp.ext
  intro i
  change ((y i + (m i : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add]
  have hm : ((m i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using
      (AddCircle.coe_zsmul (1 : ℝ) (n := m i) (x := (1 : ℝ)))
  rw [hm, add_zero]

/-- The actual extended orbit sources are integer-periodic on every parameter value. -/
theorem freeHopfOrbitSource_integer_periodic {a : ℕ} (C : Fin a → ℕ)
    {V : Type*} [Zero V] (F : ℝ × FreeHopfProduct C → V)
    (p : FreeHopfAmbientSpace C × ℝ) (y : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ) :
    freeHopfOrbitSource C F p (y + toLp 2 (fun i ↦ (m i : ℝ))) =
      freeHopfOrbitSource C F p y := by
  unfold freeHopfOrbitSource
  split_ifs with h
  · rw [freeHopfRealAction_integer_periodic]
  · rfl

/-- Actual zero-time forcing gives actual zero orbit forcing; no norm limit is assumed. -/
theorem freeHopfOrbitSource_zero_time {a : ℕ} (C : Fin a → ℕ)
    {V : Type*} [Zero V] (F : ℝ × FreeHopfProduct C → V)
    (hF : ∀ x, F (0, x) = 0) (p : FreeHopfAmbientSpace C)
    (y : EuclideanSpace ℝ (Fin a)) : freeHopfOrbitSource C F (p, 0) y = 0 := by
  unfold freeHopfOrbitSource
  split_ifs <;> simp only [hF]

/-- Actual radial orbit sources produce genuine smooth little forcing and multiplier data.

Proof: the proved native source lifting theorem gives actual finite-dimensional ambient
smoothness on the exact radial/time domain. True torus descent gives integer periodicity.
Apply the accepted arbitrary finite-parameter source-to-little theorem to these exact
sources. It constructs the actual carriers and multiplier, their original point values,
norm smoothness and genuine translated/conjugated norm smoothness. No pre-existing little
data, desired solution, inverse or compatibility is assumed.
Source: the compact local correction in lem:balanced, lines403–418. -/
theorem freeHopfOrbitSource_little_data_exists {a d N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] {α : ℝ} (J : Set ℝ) (hJ : IsOpen J)
    (sourceA : ℝ × FreeHopfProduct C →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (sourcef : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) ∞
      sourceA (J ×ˢ univ))
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ sourcef (J ×ˢ univ))
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ f : (FreeHopfAmbientSpace C × ℝ) → LittlePeriodicCAlphaFunction a N 2 α,
      ∃ A : (FreeHopfAmbientSpace C × ℝ) →
          LittlePeriodicCAlphaFunction a d 2 α →L[ℝ] LittlePeriodicCAlphaFunction a N 2 α,
        (∀ p ∈ (freeHopfAmbientDomain C : Set (FreeHopfAmbientSpace C)) ×ˢ J, ∀ y,
          (f p).val.toFun y = freeHopfOrbitSource C sourcef p y) ∧
        (∀ p ∈ (freeHopfAmbientDomain C : Set (FreeHopfAmbientSpace C)) ×ˢ J,
          ∀ (u : LittlePeriodicCAlphaFunction a d 2 α) y,
            (A p u).val.toFun y = freeHopfOrbitSource C sourceA p y (u.val.toFun y)) ∧
        ContDiffOn ℝ ∞ f ((freeHopfAmbientDomain C : Set (FreeHopfAmbientSpace C)) ×ˢ J) ∧
        ContDiffOn ℝ ∞ A ((freeHopfAmbientDomain C : Set (FreeHopfAmbientSpace C)) ×ˢ J) ∧
        ContDiffOn ℝ ∞ (fun z : (FreeHopfAmbientSpace C × ℝ) ×
            EuclideanSpace ℝ (Fin a) ↦ littlePeriodicCAlphaTranslateIsometry z.2 (f z.1))
          (((freeHopfAmbientDomain C : Set (FreeHopfAmbientSpace C)) ×ˢ J) ×ˢ univ) ∧
        ContDiffOn ℝ ∞ (fun z : (FreeHopfAmbientSpace C × ℝ) ×
            EuclideanSpace ℝ (Fin a) ↦
          (littlePeriodicCAlphaTranslateIsometry z.2).toContinuousLinearMap.comp
            ((A z.1).comp
              (littlePeriodicCAlphaTranslateIsometry (-z.2)).toContinuousLinearMap))
          (((freeHopfAmbientDomain C : Set (FreeHopfAmbientSpace C)) ×ˢ J) ×ˢ univ) := by
  exact balanced_source_little_data_exists
    ((freeHopfAmbientDomain C : Set (FreeHopfAmbientSpace C)) ×ˢ J)
    ((freeHopfAmbientDomain C).isOpen.prod hJ)
    (freeHopfOrbitSource C sourceA) (freeHopfOrbitSource C sourcef)
    (freeHopfOrbitSource_contDiffOn C J hJ sourceA hA)
    (freeHopfOrbitSource_contDiffOn C J hJ sourcef hf)
    (fun p _ y m ↦ freeHopfOrbitSource_integer_periodic C sourceA p y m)
    (fun p _ y m ↦ freeHopfOrbitSource_integer_periodic C sourcef p y m) hα0 hα1

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopfOrbitSource_contDiffOn
#print axioms GlobalEmbedding.Paper.freeHopfRealAction_integer_periodic
#print axioms GlobalEmbedding.Paper.freeHopfOrbitSource_little_data_exists
