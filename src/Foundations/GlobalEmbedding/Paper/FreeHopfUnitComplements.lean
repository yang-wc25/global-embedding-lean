import GlobalEmbedding.Paper.FreeOrderedCofactor
import GlobalEmbedding.Paper.FreeHopfProductGenerators
import GlobalEmbedding.Paper.FreeSelectorProperties
import GlobalEmbedding.Paper.FramedDistributionPartialImmersion
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth

/-!
# Actual immersive coordinates and unit complements on the genuine Hopf product

Source: `main.tex`, `thm:free`, lines421–435. DAG: `free-hopf-cofactor-adapters`.
Use the accepted genuine framed partial immersion to construct A, and the actual
ordered cofactor to construct n. The final free-jet complement uses the original
first/sorted-second index, transported only by a finite enumeration.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]

/-- The actual first Hopf derivative of any native smooth observable is native smooth.
Proof: apply the accepted smooth-orbit derivative theorem to the actual factor flow. -/
theorem freeHopfDeriv_contMDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : FreeHopfProduct C → F)
    (hf : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ f) (i : Fin a) :
    ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ (freeHopfDeriv C i f) :=
  contMDiff_orbitDeriv _ (freeHopfProductFlow_contMDiff C i) f hf

/-- The actual smooth partial immersion and its oriented unit cofactor both exist.
Proof: apply the accepted framed partial-immersion theorem to the genuine Hopf
frame. Its actual derivative images are independent by the accepted restriction
criterion and actual generator/orbit derivative identity. Apply the explicit
ordered cofactor to these genuine native smooth first columns. -/
theorem freeHopf_immersive_coordinates_unit_cofactor :
    ∃ A n : FreeHopfProduct C → EuclideanSpace ℝ (Fin (a + 1)),
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (a + 1))) ∞ A ∧
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (a + 1))) ∞ n ∧
      (∀ x, LinearIndependent ℝ (fun i ↦ freeHopfDeriv C i A x)) ∧
      (∀ x, ‖n x‖ = 1) ∧
      (∀ x i, inner ℝ (n x) (freeHopfDeriv C i A x) = 0) ∧
      (∀ x, 0 < freeOrderedVolume a
        (Fin.snoc (fun i ↦ freeHopfDeriv C i A x) (n x))) := by
  obtain ⟨A, hA, hrestr⟩ := framed_distribution_partial_immersion_exists
    (freeHopfModel C) (freeHopfFramedDistribution C)
  have hLI (x : FreeHopfProduct C) :
      LinearIndependent ℝ (fun i ↦ freeHopfDeriv C i A x) := by
    have h := (framedPartial_injective_iff (freeHopfFramedDistribution C) x
      (mfderiv (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (a + 1))) A x)).mp
        (hrestr x)
    change LinearIndependent ℝ (fun i ↦ mvfderiv (freeHopfModel C) A x
      (freeHopfGenerator C i x)) at h
    simpa only [freeHopfGenerator_mvfderiv C _ A hA x] using h
  obtain ⟨n, hn, hunit, hperp, hpos⟩ := exists_freeOrderedUnitComplement
    (freeHopfModel C) a (fun i ↦ freeHopfDeriv_contMDiff C A hA i) hLI
  exact ⟨A, n, hA, hn, hLI, hunit, hperp, hpos⟩

/-- Every actual first and sorted second Hopf column is native smooth.
Proof: apply the accepted actual orbit differentiation theorem once or twice,
according to the existing genuine column index. -/
theorem freeHopf_free_columns_contMDiff {N : ℕ}
    (F : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (k : BalancedPairingIndex a) :
    ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun x ↦ freeFlowColumns (freeHopfProductFlow C) F x k) := by
  cases k with
  | inl i => exact freeHopfDeriv_contMDiff C F hF i
  | inr ij =>
    exact freeHopfDeriv_contMDiff C _ (freeHopfDeriv_contMDiff C F hF ij.val.2) ij.val.1

/-- The actual balanced native columns are exactly the original Hopf orbit columns.
Proof: use the accepted genuine generator derivative identity at each first
column, then on the actual native smooth first derivative at each sorted pair. -/
theorem freeHopf_balanced_pairing_columns {N : ℕ}
    (F : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (x : FreeHopfProduct C) :
    balancedPairingColumns F (freeHopfGenerator C) x =
      freeFlowColumns (freeHopfProductFlow C) F x := by
  funext k
  cases k with
  | inl i => exact freeHopfGenerator_mvfderiv C i F hF x
  | inr ij =>
    have hfirst : balancedDirectionalDerivative F (freeHopfGenerator C ij.val.2) =
        freeHopfDeriv C ij.val.2 F := by
      funext y
      exact freeHopfGenerator_mvfderiv C ij.val.2 F hF y
    change balancedDirectionalDerivative
      (balancedDirectionalDerivative F (freeHopfGenerator C ij.val.2))
      (freeHopfGenerator C ij.val.1) x = _
    rw [hfirst]
    exact freeHopfGenerator_mvfderiv C ij.val.1 _
      (freeHopfDeriv_contMDiff C F hF ij.val.2) x

/-- A fixed enumeration of the existing complete index, in the exact target dimension.
This changes neither the actual columns nor their indices in the public conclusions. -/
def freeCofactorColumnOrder (a : ℕ) :
    BalancedPairingIndex a ≃ Fin (freeSymmetricColumnCount a + a) :=
  Fintype.equivFinOfCardEq (by rw [balanced_pairing_index_card]; omega)

/-- The same actual free Hopf map has a genuine global native smooth unit complement.
Proof: enumerate the original first/sorted-second index once. Its actual columns
are native smooth and independent, so the accepted actual cofactor constructs a
native smooth unit complement. Transport each orthogonality identity back to its
original individual index. No unit normal or auxiliary global orientation is assumed. -/
theorem freeHopf_unit_complement_of_free_columns
    (F : FreeHopfProduct C →
      EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)))
    (hF : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1))) ∞ F)
    (hfree : ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) F x)) :
    ∃ ν : FreeHopfProduct C →
        EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)),
      ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1))) ∞ ν ∧
      (∀ x, ‖ν x‖ = 1) ∧
      (∀ x k, inner ℝ (ν x) (freeFlowColumns (freeHopfProductFlow C) F x k) = 0) := by
  let v := fun x i ↦ freeFlowColumns (freeHopfProductFlow C) F x
    ((freeCofactorColumnOrder a).symm i)
  obtain ⟨ν, hν, hunit, hperp, _⟩ := exists_freeOrderedUnitComplement
    (freeHopfModel C) (freeSymmetricColumnCount a + a)
    (v := v) (fun i ↦ freeHopf_free_columns_contMDiff C F hF _)
    (fun x ↦ (hfree x).comp _ (freeCofactorColumnOrder a).symm.injective)
  refine ⟨ν, hν, hunit, ?_⟩
  intro x k
  simpa only [v, Equiv.symm_apply_apply] using hperp x (freeCofactorColumnOrder a k)

/-- Once the same actual map has exact partial Gram and free columns, the full original
selector predicate follows by constructing its global unit complement.
Proof: use the actual cofactor complement and assemble the unchanged predicate. -/
theorem freeHopf_selector_properties_of_gram_free
    (F : FreeHopfProduct C →
      EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)))
    (hF : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1))) ∞ F)
    (hgram : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i F x) = 1)
    (hfree : ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) F x)) :
    ∃ ν, FreeSelectorProperties (freeHopfModel C) (freeHopfProductFlow C) F ν := by
  obtain ⟨ν, hν, hunit, hperp⟩ := freeHopf_unit_complement_of_free_columns C F hF hfree
  exact ⟨ν, hF, hν, hgram, hfree, hunit, hperp⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopfDeriv_contMDiff
#print axioms GlobalEmbedding.Paper.freeHopf_immersive_coordinates_unit_cofactor
#print axioms GlobalEmbedding.Paper.freeHopf_free_columns_contMDiff
#print axioms GlobalEmbedding.Paper.freeHopf_balanced_pairing_columns
#print axioms GlobalEmbedding.Paper.freeCofactorColumnOrder
#print axioms GlobalEmbedding.Paper.freeHopf_unit_complement_of_free_columns
#print axioms GlobalEmbedding.Paper.freeHopf_selector_properties_of_gram_free
