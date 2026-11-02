import GlobalEmbedding.Paper.FreeMixedPeriodIdentity
import GlobalEmbedding.Paper.FreeInductionPolynomial
import GlobalEmbedding.Paper.MatrixPlanarSelectorProperties

/-!
# The actual induction hypothesis supplies the whole-product geometric data

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines431–475.
DAG: `free-induction-native-data`; exclusive worker W6.
The existing source split, target block, Base and Z are used literally.
-/

noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace Matrix.Norms.Elementwise

namespace GlobalEmbedding.Paper

variable {m K : ℕ} (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]

local instance freeNativeDataOldPositive (i : Fin m) :
    Fact (0 < freeHopfOldDimensions C i) := inferInstanceAs (Fact (0 < C i.castSucc))

local instance freeNativeDataMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

omit [∀ i, Fact (0 < C i)] in
private theorem old_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : FreeHopfProduct (freeHopfOldDimensions C) → V) (i : Fin m) (x : FreeHopfProduct C) :
    freeHopfDeriv C i.castSucc (fun y ↦ g (freeHopfProductSplit C y).1) x =
      freeHopfDeriv (freeHopfOldDimensions C) i g (freeHopfProductSplit C x).1 :=
  freeHopfDeriv_split_old C (fun p ↦ g p.1) i x

omit [∀ i, Fact (0 < C i)] in
private theorem last_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : PlanarHopfSphere (C (Fin.last m)) → V) (x : FreeHopfProduct C) :
    freeHopfDeriv C (Fin.last m) (fun y ↦ g (freeHopfProductSplit C y).2) x =
      orbitDeriv planarHopfFlow g (freeHopfProductSplit C x).2 :=
  freeHopfDeriv_split_last C (fun p ↦ g p.2) x

omit [∀ i, Fact (0 < C i)] in
/-- The old once-indexed first and sorted second columns pull back exactly through
W1's genuine split. W2's actual orbit-curve conjugation is applied twice, without a
new source flow or an assumed derivative interchange. Source: old H in line431. -/
theorem freeHopf_old_flowColumns_pullback
    (H : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (x : FreeHopfProduct C) :
    freeFlowColumns (fun i : Fin m ↦ freeHopfProductFlow C i.castSucc)
      (fun y ↦ H (freeHopfProductSplit C y).1) x =
    freeFlowColumns (freeHopfProductFlow (freeHopfOldDimensions C)) H
      (freeHopfProductSplit C x).1 := by
  funext j
  rcases j with i | ⟨⟨i, j⟩, hij⟩
  · exact old_deriv C H i x
  · change freeHopfDeriv C i.castSucc
      (freeHopfDeriv C j.castSucc (fun y ↦ H (freeHopfProductSplit C y).1)) x = _
    rw [show freeHopfDeriv C j.castSucc (fun y ↦ H (freeHopfProductSplit C y).1) =
      (fun y ↦ freeHopfDeriv (freeHopfOldDimensions C) j H (freeHopfProductSplit C y).1)
      from funext (old_deriv C H j)]
    exact old_deriv C (freeHopfDeriv (freeHopfOldDimensions C) j H) i x

/-- The unchanged old selector hypothesis and the actual single-sphere profile
supply all source-geometric inputs of the whole-product polynomial construction.
Native smoothness is composition with the accepted split. First and second old
columns and old Gram are actual pullbacks; factor basicness follows from literal
flow conjugation. Unit speed, acceleration and nonzero curvature on every orbit
are the same profile's properties, including its actual curvature-zero locus.
No source-geometric condition is supplied separately. Source: lines431–442. -/
theorem freeHopf_induction_geometric_data
    (H ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hIH : FreeSelectorProperties (freeHopfModel (freeHopfOldDimensions C))
      (freeHopfProductFlow (freeHopfOldDimensions C)) H ν)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : MatrixPlanarSelectorProperties f) :
    let H' := fun y : FreeHopfProduct C ↦ H (freeHopfProductSplit C y).1
    let f' := fun y : FreeHopfProduct C ↦ f (freeHopfProductSplit C y).2
    let κ := fun y : FreeHopfProduct C ↦
      planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C y).2
    ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H' ∧
    ContMDiff (freeHopfModel C) 𝓘(ℝ, Planar) ∞ f' ∧
    ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞ κ ∧
    (∀ t x, H' (freeHopfProductFlow C (Fin.last m) t x) = H' x) ∧
    (∀ (i : Fin m) t x, f' (freeHopfProductFlow C i.castSucc t x) = f' x) ∧
    (∀ x, LinearIndependent ℝ
      (freeFlowColumns (fun i : Fin m ↦ freeHopfProductFlow C i.castSucc) H' x)) ∧
    (∀ x, ‖freeHopfDeriv C (Fin.last m) f' x‖ = 1) ∧
    (∀ x, freeHopfDeriv C (Fin.last m) (freeHopfDeriv C (Fin.last m) f') x =
      κ x • planarQuarterTurn (freeHopfDeriv C (Fin.last m) f' x)) ∧
    (∀ x, ∃ s : ℝ, κ (freeHopfProductFlow C (Fin.last m) s x) ≠ 0) ∧
    (∀ x, Matrix.gram ℝ (fun i : Fin m ↦ freeHopfDeriv C i.castSucc H' x) = 1) := by
  dsimp only
  refine ⟨hIH.1.comp (contMDiff_fst.comp (freeHopfProductSplit_contMDiff C)),
    hf.smooth.comp (contMDiff_snd.comp (freeHopfProductSplit_contMDiff C)),
    hf.curvature_smooth.comp (contMDiff_snd.comp (freeHopfProductSplit_contMDiff C)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x
    rw [freeHopfProductSplit_flow_last]
  · intro i t x
    rw [freeHopfProductSplit_flow_old]
  · intro x
    rw [freeHopf_old_flowColumns_pullback]
    exact hIH.2.2.2.1 _
  · intro x
    rw [last_deriv]
    exact hf.unit_speed _
  · intro x
    rw [show freeHopfDeriv C (Fin.last m)
      (fun y ↦ f (freeHopfProductSplit C y).2) =
      (fun y ↦ orbitDeriv planarHopfFlow f (freeHopfProductSplit C y).2)
      from funext (last_deriv C f)]
    rw [last_deriv]
    exact hf.acceleration _
  · intro x
    obtain ⟨t, s, ht, hs⟩ := hf.curvature_signs (freeHopfProductSplit C x).2
    refine ⟨t, ?_⟩
    rw [freeHopfProductSplit_flow_last]
    exact ne_of_lt ht
  · intro x
    have he : (fun i : Fin m ↦ freeHopfDeriv C i.castSucc
        (fun y ↦ H (freeHopfProductSplit C y).1) x) =
      (fun i ↦ freeHopfDeriv (freeHopfOldDimensions C) i H (freeHopfProductSplit C x).1) :=
      funext (fun i ↦ old_deriv C H i x)
    rw [he]
    exact hIH.2.2.1 _

/-- The unchanged selector induction hypothesis and the same genuine matrix
moments construct the actual whole-product second correction W. All geometry is
supplied by the actual pullbacks just proved; W2's physical mixed-period identity
uses this same ν/P/Q/η/δ/A/n. W6's real second-cancellation construction then gives
one native smooth W, including the curvature-zero locus. No desired W, complete
cancellation, formal Z, mixed-period or source-basicness hypothesis is an input.
Source: thm:free, lines431–475. -/
theorem freeHopf_induction_second_correction
    (H ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hIH : FreeSelectorProperties (freeHopfModel (freeHopfOldDimensions C))
      (freeHopfProductFlow (freeHopfOldDimensions C)) H ν)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : MatrixPlanarSelectorProperties f)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (hSO : ∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin (m + 1)) ℝ)
    (hperiod : ∀ z, orbitAverage planarHopfFlow (fun w ↦ (P w).transpose * Q w) z = 0)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η)
    (hmean : ∀ z, orbitAverage planarHopfFlow η z = 0)
    (hquad : ∀ z, orbitAverage planarHopfFlow (fun w ↦
      η w ^ 2 • ((Q w).transpose * orbitDeriv planarHopfFlow Q w)) z = 0)
    (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (hnunit : ∀ x, ‖n x‖ = 1)
    (hnorth : ∀ x i, ⟪n x, freeHopfDeriv (freeHopfOldDimensions C) i A x⟫ = 0)
 :
    ∃ (W : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))
      (_hW : ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ W),
      ∀ x, freeMetricCrossTerm (freeHopfInductionBase C H f) W
        (freeHopfGeneratorSection C) x +
        balancedGeometry (freeHopfInductionZ C ν P Q η δ A n)
          (freeHopfInductionZ_contMDiff C ν hIH.2.1 P Q hP hQ η hη δ A n hA hn)
          (freeHopfGeneratorSection C) x = 0 := by
  obtain ⟨hH, hfs, hκ, hHb, hfb, hind, hu, ha, hκn, hGram⟩ :=
    freeHopf_induction_geometric_data C H ν hIH f hf
  have hZ := freeHopfInductionZ_contMDiff C ν hIH.2.1 P Q hP hQ η hη δ A n hA hn
  have hper := freeHopfInductionZ_mixed_period_zero C ν hIH.2.1 hIH.2.2.2.2.1
    P Q hP hQ hPQ hSO hperiod η hη hmean hquad δ A n hA hn hnunit hnorth
  obtain ⟨W, hW, hc⟩ := free_induction_second_correction C
    (fun y ↦ H (freeHopfProductSplit C y).1)
    (fun y ↦ f (freeHopfProductSplit C y).2)
    (freeHopfInductionZ C ν P Q η δ A n)
    (fun y ↦ planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C y).2)
    hH hfs hZ hκ hHb hfb hind hu ha hκn hper
  exact ⟨W, hW, hc⟩

/-- The original induction hypothesis and the same actual matrix moments yield
one joint native smooth polynomial with the original fixed cubic and quartic
residual. The geometric inputs are proved above, while the first cancellation and
all physical mixed periods are W2's actual whole-product theorems. The accepted
polynomial theorem constructs W; neither W nor any residual or coefficient is given.
The same H/ν/f/P/Q/η/δ/A/n and the canonical Base/Z are retained at every parameter.
Source: the actual Pε and Γ(Pε)=I+ε³S₃+ε⁴S₄ in lines474–475. -/
theorem freeHopf_induction_polynomial
    (H ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hIH : FreeSelectorProperties (freeHopfModel (freeHopfOldDimensions C))
      (freeHopfProductFlow (freeHopfOldDimensions C)) H ν)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
    (hf : MatrixPlanarSelectorProperties f)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (hSO : ∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin (m + 1)) ℝ)
    (hperiod : ∀ z, orbitAverage planarHopfFlow (fun w ↦ (P w).transpose * Q w) z = 0)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η)
    (hmean : ∀ z, orbitAverage planarHopfFlow η z = 0)
    (hquad : ∀ z, orbitAverage planarHopfFlow (fun w ↦
      η w ^ 2 • ((Q w).transpose * orbitDeriv planarHopfFlow Q w)) z = 0)
    (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (hnunit : ∀ x, ‖n x‖ = 1)
    (hnorth : ∀ x i, ⟪n x, freeHopfDeriv (freeHopfOldDimensions C) i A x⟫ = 0)
 :
    let F0 := freeHopfInductionBase C H f
    let Z := freeHopfInductionZ C ν P Q η δ A n
    let hF0 := freeHopfInductionBase_contMDiff C H hIH.1 f hf.smooth
    let hZ := freeHopfInductionZ_contMDiff C ν hIH.2.1 P Q hP hQ η hη δ A n hA hn
    ∃ (W : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))
      (hW : ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ W),
      ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞
        (fun p : ℝ × FreeHopfProduct C ↦ freePolynomialFamily F0 Z W p.1 p.2) ∧
      (∀ ε x, balancedGeometry (freePolynomialFamily F0 Z W ε)
        (freePolynomialFamily_contMDiff F0 Z W hF0 hZ hW ε)
        (freeHopfGeneratorSection C) x =
          1 + ε ^ 3 • freeMetricCrossTerm Z W (freeHopfGeneratorSection C) x +
            ε ^ 4 • balancedGeometry W hW (freeHopfGeneratorSection C) x) ∧
      (∀ i j, ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞
        (fun x ↦ freeMetricCrossTerm Z W (freeHopfGeneratorSection C) x i j)) ∧
      (∀ i j, ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞
        (fun x ↦ balancedGeometry W hW (freeHopfGeneratorSection C) x i j)) := by
  obtain ⟨hH, hfs, hκ, hHb, hfb, hind, hu, ha, hκn, hGram⟩ :=
    freeHopf_induction_geometric_data C H ν hIH f hf
  have hZ := freeHopfInductionZ_contMDiff C ν hIH.2.1 P Q hP hQ η hη δ A n hA hn
  have hper := freeHopfInductionZ_mixed_period_zero C ν hIH.2.1 hIH.2.2.2.2.1
    P Q hP hQ hPQ hSO hperiod η hη hmean hquad δ A n hA hn hnunit hnorth
  have hlin := freeHopfInduction_first_variation_zero C H ν hIH f hf.smooth
    P Q hP hQ hPQ η hη δ A n hA hn
  exact free_induction_polynomial C
    (fun y ↦ H (freeHopfProductSplit C y).1)
    (fun y ↦ f (freeHopfProductSplit C y).2)
    (freeHopfInductionZ C ν P Q η δ A n)
    (fun y ↦ planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C y).2)
    hH hfs hZ hκ hHb hfb hind hu ha hκn hper hGram hlin

#print axioms freeHopf_old_flowColumns_pullback
#print axioms freeHopf_induction_geometric_data
#print axioms freeHopf_induction_second_correction
#print axioms freeHopf_induction_polynomial

end GlobalEmbedding.Paper
