import GlobalEmbedding.Paper.IncrementsActualTransverseReconstruction
import Mathlib.Analysis.Complex.Basic

/-!
# Actual real first-order coefficients of the original mode system (6.2)

Source: `main.tex`, lem:increments, lines 617–635.
DAG: `increments-mode-first-order-coefficient-realization`. Exclusive worker W2.
The original smooth F and an actual coordinate parametrization c determine Gamma,
true B and the accepted transverse J. There is no new section or normed carrier.
Coefficient smoothness and quantitative weighted bounds remain separate obligations.
-/

noncomputable section
open Manifold
open scoped ContDiff
namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "P" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ P

/-- Actual tangent coordinate directions, obtained by differentiating c.
Source: adapted coordinates x¹=psi in original (6.2). -/
def incrementsModeCoordinateDirections (c : D → M) (x : D) (i : Fin (m + 1)) :
    TangentSpace I (c x) :=
  mfderiv 𝓘(ℝ, D) I c x
    ((tangentSpaceCastModel 𝓘(ℝ, D) x).symm (EuclideanSpace.single i 1))

/-- The actual induced Gram Christoffel coefficient of F in coordinates c.
Source: Gamma in (6.2); its Koszul identification is already accepted. -/
def incrementsModeGamma (F : M → EuclideanSpace ℝ (Fin N)) (c : D → M)
    (x : D) (i j : Fin (m + 1)) : D :=
  let A := fderiv ℝ (F ∘ c) x
  (A.adjoint.comp A).inverse (A.adjoint
    (fderiv ℝ (fderiv ℝ (F ∘ c)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)))

/-- The SAME original true normal second form on actual coordinate directions.
Source: B in (6.2), without replacing it by supplied tensor data. -/
def incrementsModeSecondForm (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (x : D) (i j : Fin (m + 1)) : normalSpace (I := I) F (c x) :=
  trueSecondForm F hF (c x) (symmetricSquareProduct (TangentSpace I (c x))
    (incrementsModeCoordinateDirections c x i) (incrementsModeCoordinateDirections c x j))

/-- J is the accepted actual transverse reconstruction for these SAME directions.
Source: J=beta*(beta beta*)^-1 in (6.2). No new inverse is constructed. -/
def incrementsModeCoordinateJ (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M) (x : D) :
    Tdata →L[ℝ] normalSpace (I := I) F (c x) :=
  incrementsTransverseRightInverse F hF (c x)
    (fun a ↦ incrementsModeCoordinateDirections c x a.succ)

/-- Native coordinate evaluation of a genuine first jet: (Du e_i)_j.
Source: the partial-derivative coefficients in (6.2). -/
def incrementsModeJetComponent (i j : Fin (m + 1)) : (D →L[ℝ] D) →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (ContinuousLinearMap.apply ℝ D (EuclideanSpace.single i 1))

/-- Zeroth-order part of the actual transverse T: -Gamma_ab.u.
Source: T in (6.2); the original once-sorted data coordinates are retained. -/
def incrementsModeTransverseValue (F : M → EuclideanSpace ℝ (Fin N)) (c : D → M)
    (x : D) : D →L[ℝ] Tdata :=
  (EuclideanSpace.equiv P ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun q ↦ -(innerSL ℝ
      (incrementsModeGamma F c x q.val.1.succ q.val.2.succ)))

/-- First-jet part of the actual transverse T, with its original factor one half.
Source: T_ab=(partial_a u_b+partial_b u_a)/2-Gamma_ab.u in (6.2). -/
def incrementsModeTransverseJet : (D →L[ℝ] D) →L[ℝ] Tdata :=
  (EuclideanSpace.equiv P ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun q ↦ (1 / 2 : ℝ) •
      (incrementsModeJetComponent q.val.1.succ q.val.2.succ +
        incrementsModeJetComponent q.val.2.succ q.val.1.succ))

/-- The actual transverse differential expression of the original u.
Source: T(u) immediately before (6.2), with actual native fderiv. -/
def incrementsModeTransverseTensor (F : M → EuclideanSpace ℝ (Fin N)) (c : D → M)
    (u : D → D) (x : D) : Tdata :=
  WithLp.toLp 2 fun q ↦
    ((fderiv ℝ u x (EuclideanSpace.single q.val.1.succ 1)) q.val.2.succ +
      (fderiv ℝ u x (EuclideanSpace.single q.val.2.succ 1)) q.val.1.succ) / 2 -
      inner ℝ (incrementsModeGamma F c x q.val.1.succ q.val.2.succ) (u x)

omit [TopologicalSpace M] in
/-- Splitting actual T into value and first-jet coefficients is a proved identity.
Source: the coefficient realization of (6.2), not a desired linearity assumption. -/
theorem incrementsModeTransverseTensor_split
    (F : M → EuclideanSpace ℝ (Fin N)) (c : D → M) (u : D → D) (x : D) :
    incrementsModeTransverseTensor F c u x =
      incrementsModeTransverseValue F c x (u x) +
        incrementsModeTransverseJet (fderiv ℝ u x) := by
  ext q
  simp [incrementsModeTransverseTensor, incrementsModeTransverseValue,
    incrementsModeTransverseJet, incrementsModeJetComponent]
  ring

/-- Original (6.2) row multiplicity: one in 11, two in each mixed row. -/
def incrementsModeRowWeight (i : Fin (m + 1)) : ℝ := Fin.cases 1 (fun _ ↦ 2) i

/-- Actual zeroth-order coefficient B(x) of the SAME original reduced mode operator.
Source: Gamma and J T(value) terms in (6.2). All maps are native finite CLMs. -/
def incrementsModeFirstOrderB (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M) (x : D) :
    D →L[ℝ] D :=
  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦
      -(incrementsModeRowWeight i • innerSL ℝ (incrementsModeGamma F c x 0 i)) -
        incrementsModeRowWeight i • ((innerSL ℝ (incrementsModeSecondForm F hF c x 0 i)).comp
          ((incrementsModeCoordinateJ F hF c x).comp (incrementsModeTransverseValue F c x))))

/-- Actual first-jet coefficient A(x) of the SAME original reduced mode operator.
Source: the partial terms and J T(first jet) terms in (6.2). -/
def incrementsModeFirstOrderA (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M) (x : D) :
    (D →L[ℝ] D) →L[ℝ] D :=
  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦
      Fin.cases (incrementsModeJetComponent 0 0)
        (fun a ↦ incrementsModeJetComponent 0 a.succ + incrementsModeJetComponent a.succ 0) i -
      incrementsModeRowWeight i • ((innerSL ℝ (incrementsModeSecondForm F hF c x 0 i)).comp
        ((incrementsModeCoordinateJ F hF c x).comp incrementsModeTransverseJet)))

/-- The original reduced real operator, defined by its actual 11 and mixed formulas.
Source: L in (6.2); totalized fderiv is never asserted linear on arbitrary functions. -/
def incrementsModeReducedOperator (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (u : D → D) (x : D) : D :=
  WithLp.toLp 2 fun i ↦
    Fin.cases ((fderiv ℝ u x (EuclideanSpace.single 0 1)) 0)
      (fun a ↦ (fderiv ℝ u x (EuclideanSpace.single 0 1)) a.succ +
        (fderiv ℝ u x (EuclideanSpace.single a.succ 1)) 0) i -
    incrementsModeRowWeight i * inner ℝ (incrementsModeGamma F c x 0 i) (u x) -
    incrementsModeRowWeight i * inner ℝ (incrementsModeSecondForm F hF c x 0 i)
      (incrementsModeCoordinateJ F hF c x (incrementsModeTransverseTensor F c u x))

/-- The SAME geometric reduced operator is literally the accepted first-order form.
Source: (6.2), the bridge to canonical IncrementsWeightedIterate.
Proof: use the proved actual T split, then native CLM and inner additivity. -/
theorem incrementsModeReducedOperator_first_order
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (u : D → D) (x : D) :
    incrementsModeReducedOperator F hF c u x =
      incrementsModeFirstOrderB F hF c x (u x) +
        incrementsModeFirstOrderA F hF c x (fderiv ℝ u x) := by
  ext i
  simp only [incrementsModeReducedOperator, incrementsModeTransverseTensor_split,
    map_add, inner_add_right]
  refine Fin.cases ?_ (fun a ↦ ?_) i <;>
    simp [incrementsModeFirstOrderB, incrementsModeFirstOrderA, incrementsModeJetComponent,
      incrementsModeRowWeight] <;> ring

/-- The original h_H is the once-sorted transverse part of the SAME source h.
Source: h_H in (6.2); no desired source components are supplied. -/
def incrementsModeTransverseSource (h : D → Fin (m + 1) → Fin (m + 1) → ℝ) (x : D) :
    Tdata := WithLp.toLp 2 fun q ↦ h x q.val.1.succ q.val.2.succ

/-- The actual source k, with the original11 half and mixed Jh_H coefficient -1.
Source: k in (6.2), evaluated on SAME h and original-normal free amplitude vf. -/
def incrementsModeSource (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (h : D → Fin (m + 1) → Fin (m + 1) → ℝ)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (x : D) : D :=
  WithLp.toLp 2 fun i ↦ Fin.cases (h x 0 0 / 2) (fun a ↦ h x 0 a.succ) i +
    incrementsModeRowWeight i * inner ℝ (incrementsModeSecondForm F hF c x 0 i) (vf x) -
    (incrementsModeRowWeight i / 2) * inner ℝ (incrementsModeSecondForm F hF c x 0 i)
      (incrementsModeCoordinateJ F hF c x (incrementsModeTransverseSource h x))

/-- The actual constructed source has the original11 coefficient -1/2 on Jh_H.
Source: the first source row of (6.2). -/
theorem incrementsModeSource_first
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (h : D → Fin (m + 1) → Fin (m + 1) → ℝ)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (x : D) :
    incrementsModeSource F hF c h vf x 0 = h x 0 0 / 2 +
      inner ℝ (incrementsModeSecondForm F hF c x 0 0) (vf x) -
      inner ℝ (incrementsModeSecondForm F hF c x 0 0)
        (incrementsModeCoordinateJ F hF c x (incrementsModeTransverseSource h x)) / 2 := by
  simp [incrementsModeSource, incrementsModeRowWeight]
  ring

/-- The mixed source coefficient of Jh_H is minus ONE, as in the original paper.
Source: the mixed source row of (6.2), not minus one half or minus two. -/
theorem incrementsModeSource_mixed
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (h : D → Fin (m + 1) → Fin (m + 1) → ℝ)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (x : D) (a : Fin m) :
    incrementsModeSource F hF c h vf x a.succ = h x 0 a.succ +
      2 * inner ℝ (incrementsModeSecondForm F hF c x 0 a.succ) (vf x) -
      inner ℝ (incrementsModeSecondForm F hF c x 0 a.succ)
        (incrementsModeCoordinateJ F hF c x (incrementsModeTransverseSource h x)) := by
  simp [incrementsModeSource, incrementsModeRowWeight]

local notation "Cdata" => Fin (m + 1) → ℂ

/-- Native component real parts, in the existing real Euclidean coordinates.
Source: real/imaginary realization of the original complex system (6.2). -/
def incrementsModeRealPart : Cdata →L[ℝ] D :=
  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ Complex.reCLM.comp (ContinuousLinearMap.proj i))

/-- Native component imaginary parts, with all existing norms retained.
Source: real/imaginary realization of (6.2); no isometry is asserted. -/
def incrementsModeImagPart : Cdata →L[ℝ] D :=
  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ Complex.imCLM.comp (ContinuousLinearMap.proj i))

/-- Native component real inclusion into the already used finite complex target.
Source: the complex amplitude of (6.2), not a new module of sections. -/
def incrementsModeComplexInclude : D →L[ℝ] Cdata :=
  ContinuousLinearMap.pi fun i ↦ Complex.ofRealCLM.comp (EuclideanSpace.proj i)

/-- The actual B coefficient on the original finite complex components.
It applies the SAME constructed real geometric B to the two actual channels. -/
def incrementsModeComplexFirstOrderB (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M) (x : D) :
    Cdata →L[ℝ] Cdata :=
  incrementsModeComplexInclude.comp
      ((incrementsModeFirstOrderB F hF c x).comp incrementsModeRealPart) +
    Complex.I • incrementsModeComplexInclude.comp
      ((incrementsModeFirstOrderB F hF c x).comp incrementsModeImagPart)

/-- The actual A coefficient on the original finite complex first jets.
Native continuous composition extracts each channel of the SAME actual first jet. -/
def incrementsModeComplexFirstOrderA (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M) (x : D) :
    (D →L[ℝ] Cdata) →L[ℝ] Cdata :=
  (incrementsModeComplexInclude.comp (incrementsModeFirstOrderA F hF c x)).comp
      ((ContinuousLinearMap.compL ℝ D Cdata D) incrementsModeRealPart) +
    Complex.I •
      (incrementsModeComplexInclude.comp (incrementsModeFirstOrderA F hF c x)).comp
        ((ContinuousLinearMap.compL ℝ D Cdata D) incrementsModeImagPart)

/-- The SAME original reduced operator on its real and imaginary amplitude fields.
This is the componentwise real geometric operator, not a supplied complex solver. -/
def incrementsModeComplexReducedOperator (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (u : D → Cdata) (x : D) : Cdata :=
  incrementsModeComplexInclude
      (incrementsModeReducedOperator F hF c (fun y ↦ incrementsModeRealPart (u y)) x) +
    Complex.I • incrementsModeComplexInclude
      (incrementsModeReducedOperator F hF c (fun y ↦ incrementsModeImagPart (u y)) x)

/-- Exact complex-target first-order realization for the SAME differentiable amplitude.
Native chain rules for real/imaginary CLMs and the proved actual real coefficient
identity give precisely B(x)u(x)+A(x)Du(x), matching the canonical iterate interface.
No totalized derivative linearity on arbitrary nonsmooth functions is asserted. -/
theorem incrementsModeComplexReducedOperator_first_order
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (u : D → Cdata) (x : D) (hu : DifferentiableAt ℝ u x) :
    incrementsModeComplexReducedOperator F hF c u x =
      incrementsModeComplexFirstOrderB F hF c x (u x) +
        incrementsModeComplexFirstOrderA F hF c x (fderiv ℝ u x) := by
  have hr : fderiv ℝ (fun y ↦ incrementsModeRealPart (u y)) x =
      incrementsModeRealPart.comp (fderiv ℝ u x) :=
    (incrementsModeRealPart.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  have hi : fderiv ℝ (fun y ↦ incrementsModeImagPart (u y)) x =
      incrementsModeImagPart.comp (fderiv ℝ u x) :=
    (incrementsModeImagPart.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  rw [incrementsModeComplexReducedOperator, incrementsModeReducedOperator_first_order,
    incrementsModeReducedOperator_first_order]
  rw [hr, hi]
  simp only [incrementsModeComplexFirstOrderB, incrementsModeComplexFirstOrderA,
    add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.compL_apply, map_add, smul_add]
  abel

end GlobalEmbedding.Paper
