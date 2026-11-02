import GlobalEmbedding.Paper.FreeSymmetricColumnCount
import GlobalEmbedding.Paper.PlanarPeriodOneCalculus
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# One fixed genuine Euclidean block coordinate map for F₀, Z and W

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 431–440 and 472–475.
DAG node: `free-induction-euclidean-blocks`. The target always has its actual l2 norm.
-/

noncomputable section

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The actual old, planar and appended coordinate indices, reordered into Fin D.
This is solely a fixed target coordinate map, never another Hopf source carrier.
Source: F₀=(H,f,0_m) and W=(W_H,uv+bJ₂v,0_m) in the source. -/
def freeInductionIndexEquiv (K m : ℕ) :
    (Fin K ⊕ (Fin 2 ⊕ Fin m)) ≃ Fin (K + (2 + m)) :=
  (Equiv.sumCongr (Equiv.refl (Fin K)) (finSumFinEquiv :
    (Fin 2 ⊕ Fin m) ≃ Fin (2 + m))).trans finSumFinEquiv

/-- The same reindexing as a genuine Euclidean linear isometry. Both sides use l2;
no max-norm product is substituted for the actual ambient Euclidean space. -/
def freeInductionBlockEquiv (K m : ℕ) :
    EuclideanSpace ℝ (Fin K ⊕ (Fin 2 ⊕ Fin m)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (K + (2 + m))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (freeInductionIndexEquiv K m)

/-- The literal target block vector (old, planar, extra) used by all three maps.
The three inputs are inserted as coordinates of one actual Euclidean l2 vector. -/
def freeInductionBlock (K m : ℕ) (h : EuclideanSpace ℝ (Fin K))
    (p : Planar) (r : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (K + (2 + m))) :=
  freeInductionBlockEquiv K m (WithLp.toLp 2 (Sum.elim h (Sum.elim p r)))

/-- The actual Euclidean coordinate of the fixed block map is its original input
coordinate. This follows from the genuine reindexing equivalence and its inverse law.
Source: the literal target block coordinates at lines 431 and 473. -/
theorem freeInductionBlock_coordinate (K m : ℕ) (h : EuclideanSpace ℝ (Fin K))
    (p : Planar) (r : EuclideanSpace ℝ (Fin m)) (j : Fin K ⊕ (Fin 2 ⊕ Fin m)) :
    freeInductionBlock K m h p r (freeInductionIndexEquiv K m j) =
      Sum.elim h (Sum.elim p r) j := by
  simp [freeInductionBlock, freeInductionBlockEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- The target block map has exactly the sum of the three actual Euclidean inner
products. First use the actual linear isometry, then separate the genuine Sum-indexed
inner-product sum. Source: the orthogonal target blocks of F₀/Z/W in the induction. -/
theorem freeInductionBlock_inner (K m : ℕ) (h h' : EuclideanSpace ℝ (Fin K))
    (p p' : Planar) (r r' : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (freeInductionBlock K m h p r) (freeInductionBlock K m h' p' r') =
      inner ℝ h h' + (inner ℝ p p' + inner ℝ r r') := by
  unfold freeInductionBlock
  rw [(freeInductionBlockEquiv K m).inner_map_map]
  simp only [PiLp.inner_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]

/-- The fixed actual block map preserves native smoothness of all three component
maps on any native source model. Assemble actual scalar coordinates, then apply the
same genuine fixed Euclidean linear isometry. Source: the smooth F₀/Z/W maps. -/
theorem freeInductionBlock_contMDiff
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] (K m : ℕ)
    (h : M → EuclideanSpace ℝ (Fin K)) (p : M → Planar)
    (r : M → EuclideanSpace ℝ (Fin m))
    (hh : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ h)
    (hp : ContMDiff I 𝓘(ℝ, Planar) ∞ p)
    (hr : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ r) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞
      (fun x ↦ freeInductionBlock K m (h x) (p x) (r x)) := by
  apply (freeInductionBlockEquiv K m).toContinuousLinearEquiv.contDiff.contMDiff.comp
  let e := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin K ⊕ (Fin 2 ⊕ Fin m) ↦ ℝ)).symm
  apply e.contDiff.contMDiff.comp
  apply contMDiff_pi_module_iff.mpr
  intro j
  rcases j with i | (i | i)
  · exact (EuclideanSpace.proj i).contDiff.contMDiff.comp hh
  · exact (EuclideanSpace.proj i).contDiff.contMDiff.comp hp
  · exact (EuclideanSpace.proj i).contDiff.contMDiff.comp hr

/-- Actual real derivatives pass through the same fixed target block map. Assemble
the genuine coordinate derivatives by the Pi derivative theorem and compose with the
two fixed genuine continuous linear equivalences. This computes the derivative of
the actual vector, rather than postulating formal block differentiation.
Source: actual first/second columns of F₀/Z/W in lines 431–475. -/
theorem freeInductionBlock_hasDerivAt (K m : ℕ)
    (h : ℝ → EuclideanSpace ℝ (Fin K)) (p : ℝ → Planar)
    (r : ℝ → EuclideanSpace ℝ (Fin m))
    (h' : EuclideanSpace ℝ (Fin K)) (p' : Planar) (r' : EuclideanSpace ℝ (Fin m))
    (t : ℝ) (hh : HasDerivAt h h' t) (hp : HasDerivAt p p' t)
    (hr : HasDerivAt r r' t) :
    HasDerivAt (fun s ↦ freeInductionBlock K m (h s) (p s) (r s))
      (freeInductionBlock K m h' p' r') t := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin K ⊕ (Fin 2 ⊕ Fin m) ↦ ℝ)).symm
  have hc : HasDerivAt (fun s ↦ Sum.elim (h s) (Sum.elim (p s) (r s)))
      (Sum.elim h' (Sum.elim p' r')) t := by
    apply hasDerivAt_pi.mpr
    intro j
    rcases j with i | (i | i)
    · exact (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t hh
    · exact (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t hp
    · exact (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t hr
  exact (freeInductionBlockEquiv K m).toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t
    (e.hasFDerivAt.comp_hasDerivAt t hc)

/-- The literal orbit derivative of the actual block is the block of the three
actual orbit derivatives. Apply the preceding genuine derivative theorem to the
native smooth component orbit maps. No alternative source flow is introduced.
Source: the actual metric and free columns of F₀/Z/W in the induction. -/
theorem freeInductionBlock_orbitDeriv
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] (R : PeriodOneSmoothFlow I M)
    (K m : ℕ) (h : M → EuclideanSpace ℝ (Fin K)) (p : M → Planar)
    (r : M → EuclideanSpace ℝ (Fin m))
    (hh : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ h)
    (hp : ContMDiff I 𝓘(ℝ, Planar) ∞ p)
    (hr : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ r) (x : M) :
    orbitDeriv R.flow (fun y ↦ freeInductionBlock K m (h y) (p y) (r y)) x =
      freeInductionBlock K m (orbitDeriv R.flow h x) (orbitDeriv R.flow p x)
        (orbitDeriv R.flow r x) := by
  have dh := hasDerivAt_orbit R.flow R.smooth R.flow_add h hh 0 x
  have dp := hasDerivAt_orbit R.flow R.smooth R.flow_add p hp 0 x
  have dr := hasDerivAt_orbit R.flow R.smooth R.flow_add r hr 0 x
  have hd := freeInductionBlock_hasDerivAt K m _ _ _ _ _ _ 0 dh dp dr
  simpa only [orbitDeriv, R.flow_zero] using hd.deriv

/-- The actual block dimension is the original successor target dimension. The
symmetric-square count is choose(m+1,2); Pascal's identity gives its genuine successor
recurrence. The remaining equality is addition of the actual three block dimensions.
Source: D=s_m+2m+3=s_(m+1)+m+2 at line 433. -/
theorem free_induction_target_dimension (m : ℕ) :
    (freeSymmetricColumnCount m + m + 1) + (2 + m) =
      freeSymmetricColumnCount (m + 1) + (m + 1) + 1 := by
  have hs : freeSymmetricColumnCount (m + 1) = freeSymmetricColumnCount m + (m + 1) := by
    simp only [freeSymmetricColumnCount, Sym2.card, Fintype.card_fin]
    simpa only [Nat.choose_one_right, Nat.reduceAdd, Nat.add_comm] using
      Nat.choose_succ_succ' (m + 1) 1
  omega

#print axioms freeInductionBlock_inner
#print axioms freeInductionBlock_contMDiff
#print axioms free_induction_target_dimension
#print axioms freeInductionBlock_hasDerivAt
#print axioms freeInductionBlock_orbitDeriv

end GlobalEmbedding.Paper
