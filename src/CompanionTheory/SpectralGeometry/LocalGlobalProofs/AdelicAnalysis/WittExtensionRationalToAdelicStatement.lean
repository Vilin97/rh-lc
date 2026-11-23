module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.UnitChoice
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightMulActionLawsStatement
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianDiagonalisation
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionDiagonalGramTuples
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixedQuadraticMemBase

section

@[expose] public section

theorem UpperTheory.fixed_quadratic_mem_base :
    ∀ {F E : Type} [Field F] [Field E] [Algebra F E], Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (α : E), σ α ≠ α → ∀ x, σ x = x → x ∈ (algebraMap F E).range := by
  intro F E _ _ _ h σ α hα x hx
  by_contra hxr
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have li : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hxr
      refine ⟨-(s / t), ?_⟩
      have hst' : algebraMap F E s + algebraMap F E t * x = 0 := by
        simpa [Algebra.smul_def] using hst
      have ht' : algebraMap F E t ≠ 0 := by
        simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      linear_combination -hst'
    subst ht
    simp only [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
    exact ⟨by simpa using hst, rfl⟩
  have hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by simp [h])
  have hmem : α ∈ Submodule.span F (Set.range ![(1 : E), x]) := by
    rw [hspan]; exact Submodule.mem_top
  refine hα ?_
  clear hα
  induction hmem using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    fin_cases i
    · simp
    · simpa using hx
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
  | smul c a _ ha => rw [map_smul, ha]
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagHermitian

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Gka4.diag_hermitian :
    ∀ (F E : Type) [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] (σ : E →ₐ[F] E),
      HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ →
        ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E),
          HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ T →
            ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ),
              HeckeCharacterZeroLocus.SiegelWeilU.cT (↑σ : E →+* E) (↑g : Matrix (Fin n) (Fin n) E) * T * (↑g : Matrix (Fin n) (Fin n) E) =
                Matrix.diagonal fun (i : Fin n) ↦ (Algebra.algebraMap F E : F → E) (↑(D i) : F) := by
  intro F E _ _ _ _ _ σ hCM n T hT
  obtain ⟨-, hC, h2, hτ⟩ := hCM
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hτ τ, hτ τ, star_star]
  have hnr : ¬ NumberField.ComplexEmbedding.IsReal τ := by
    intro hr
    have := hC.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff] at this
    exact this hr
  obtain ⟨α, hα⟩ : ∃ α, σ α ≠ α := by
    by_contra hcon
    push_neg at hcon
    apply hnr
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have := hτ τ x
    rw [hcon x] at this
    exact this.symm
  have hfix := UpperTheory.fixed_quadratic_mem_base h2 σ α hα
  obtain ⟨g, D, h⟩ := UpperTheory.hermitian_diagonalisation σ hinv hfix n T hT.1 hT.2
  exact ⟨g, D, h⟩
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormDiagonalizesOverField

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AlgDiag

theorem diag_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), IsHermND σ T → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g = Matrix.diagonal fun i => algebraMap F E (D i : F) :=
  _root_.UpperTheory.Reformulated.B.Gka4.diag_hermitian

end GlobalTheory.CompanionTheory.SW.AlgDiag
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionDiagonalGramTuplesStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.witt_extension_diagonal_gram_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R], PIW.AdelicOrbitU.UnitChoice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (D : Fin n → Rˣ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D i : R)) → gramR R σ J Y = gramR R σ J X → ∃ h : HA R σ J, actW R σ J h X = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag | exact GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag | (intros; apply GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicOrbitOfRationalTuple

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TransUC

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem cT_map_inclR (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) E) :
    cT (sigR R σ) (g.map (inclR R)) = (cT (σ : E →+* E) g).map (inclR R) := by
  ext a b
  simp [cT, sigR_inclR]

theorem gramR_ratTup (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) : gramR R σ J (ratTup R X) = (gramE σ J X).map (inclR R) := by
  ext a b

  simp [gramR, hR, hform, gramE, hE, ratTup, JR, map_sum, map_mul, sigR_inclR]

theorem gramE_herm (σ : E →ₐ[F] E) (hσ : ∀ x : E, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → E) (a b : Fin n) :
    σ (gramE σ J X b a) = gramE σ J X a b := by

  simp only [gramE, hE, hform, map_sum, map_mul, RingHom.coe_coe, AlgHom.commutes]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hσ, hJ]
  ring

theorem inclR_algebraMap (d : F) :
    inclR (E := E) R (algebraMap F E d) = algebraMap R (R ⊗[F] E) (algebraMap F R d) := by
  change (1 : R) ⊗ₜ[F] (algebraMap F E d) = (algebraMap F R d) ⊗ₜ[F] (1 : E)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

end SlopeTestRemainingChoices

theorem trans_uc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R],
    PIW.AdelicOrbitU.UnitChoice R → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (X : Fin n → Fin M → E) (Y : Fin n → Fin M → R ⊗[F] E), (gramE σ J X).det ≠ 0 →
    gramR R σ J Y = (gramE σ J X).map (inclR R) →
    ∃ h : HA R σ J, actW R σ J h (ratTup R X) = Y := by
  intro F E _ _ _ _ _ σ hCM R _ _ uc n M J hJ X Y hdet hY
  have hσ : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  have hT : IsHermND σ (gramE σ J X) := ⟨gramE_herm σ hσ J hJ.1 X, hdet⟩
  obtain ⟨g, D, hg⟩ := GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian F E σ hCM n _ hT
  set G : Matrix (Fin n) (Fin n) (R ⊗[F] E) := (g : Matrix (Fin n) (Fin n) E).map (inclR R) with hG
  set G' : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
    ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (inclR R) with hG'
  have hGG' : G * G' = 1 := by
    have h1 : (g : Matrix (Fin n) (Fin n) E) * ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 :=
      Units.mul_inv g
    have h2 := congrArg (fun A : Matrix (Fin n) (Fin n) E => A.map (inclR (F := F) R)) h1
    simp only [Matrix.map_mul] at h2
    rw [hG, hG', h2, Matrix.map_one _ (map_zero _) (map_one _)]
  let D' : Fin n → Rˣ := fun i => Units.map (algebraMap F R).toMonoidHom (D i)
  have hdiag : cT (sigR R σ) G * (gramE σ J X).map (inclR R) * G =
      Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R)) := by
    rw [hG, cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hg]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [D', inclR_algebraMap]
    · simp [Matrix.diagonal_apply_ne _ hab, hab]
  have P := fun (Z : Fin n → Fin M → R ⊗[F] E) (H H' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =>
    GlobalTheory.T.gram_right_mul_action_laws F E σ hCM R M n J Z H H'
  have hX1 : gramR R σ J (rmul R (ratTup R X) G) =
      Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R)) := by
    rw [(P _ G G).1, gramR_ratTup, hdiag]
  have hY1 : gramR R σ J (rmul R Y G) = gramR R σ J (rmul R (ratTup R X) G) := by
    rw [hX1, (P _ G G).1, hY, hdiag]
  obtain ⟨h, hh⟩ := GlobalTheory.T.witt_extension_diagonal_gram_tuples F E σ hCM R uc M J hJ n D' _ _ hX1 hY1
  refine ⟨h, ?_⟩
  have undo : ∀ Z : Fin n → Fin M → R ⊗[F] E, rmul R (rmul R Z G) G' = Z := by
    intro Z
    rw [(P Z G G').2.1, hGG', (P Z G G').2.2.1]
  calc actW R σ J h (ratTup R X)
      = actTup R (HA.mat R σ J h) (rmul R (rmul R (ratTup R X) G) G') := by
        rw [undo]; rfl
    _ = rmul R (actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G)) G' :=
        (P _ G' G').2.2.2 _
    _ = rmul R (rmul R Y G) G' := by
        rw [show actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G) = rmul R Y G from hh]
    _ = Y := undo Y

end GlobalTheory.CompanionTheory.SW.TransUC
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicOrbitOfRationalTupleStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adelic_orbit_of_rational_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R], PIW.AdelicOrbitU.UnitChoice R → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (X : Fin n → Fin M → E) (Y : Fin n → Fin M → R ⊗[F] E), (gramE σ J X).det ≠ 0 → gramR R σ J Y = (gramE σ J X).map (inclR R) → ∃ h : HA R σ J, actW R σ J h (ratTup R X) = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.TransUC.trans_uc | exact GlobalTheory.CompanionTheory.SW.TransUC.trans_uc | (intros; apply GlobalTheory.CompanionTheory.SW.TransUC.trans_uc <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionRationalToAdelic

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TransA

theorem trans_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (X : Fin n → Fin M → E) (Y : Fin n → Fin M → AF F ⊗[F] E), (gramE σ J X).det ≠ 0 →
    gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) →
    ∃ h : HA (AF F) σ J, actW (AF F) σ J h (ratTup (AF F) X) = Y :=
  fun F E _ _ _ _ _ σ hcm M J hJ n =>
    GlobalTheory.T.adelic_orbit_of_rational_tuple F E σ hcm (AF F) (PIW.AdelicOrbitU.stP F) n M J hJ

end GlobalTheory.CompanionTheory.SW.TransA
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionRationalToAdelicStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.witt_extension_rational_to_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : Fin n → Fin M → E) (Y : Fin n → Fin M → AF F ⊗[F] E), (gramE σ J X).det ≠ 0 → gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) → ∃ h : HA (AF F) σ J, actW (AF F) σ J h (ratTup (AF F) X) = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.TransA.trans_adelic | exact GlobalTheory.CompanionTheory.SW.TransA.trans_adelic | (intros; apply GlobalTheory.CompanionTheory.SW.TransA.trans_adelic <;> assumption)
end
end
