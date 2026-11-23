module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DvdOfPhiEqZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialChineseRemainder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormSignatureRealisation
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvolutionCompatiblePolynomialStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassFirstStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassSecondStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassThirdStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveHermitianPolynomialStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialChineseRemainderStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.exists_polynomial_chinese_remainder : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X], ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := by
  first | exact @GlobalTheory.CompanionTheory.EllCRT.main | exact GlobalTheory.CompanionTheory.EllCRT.main | (intros; apply GlobalTheory.CompanionTheory.EllCRT.main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteNonsplitSignPlaces

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section
namespace GlobalTheory.CompanionTheory.FinSign

theorem ordL_eq_zero_of_v_eq_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L}
    (h : Valued.v x = 1) : ordL x = 0 := by
  unfold ordL
  rw [dite_eq_right (by rw [h]; exact one_ne_zero)]
  simp [h]
  rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E) (H₀ : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ P₁ : E[X], {w : Pl E | ¬ IsSplitAt w ∧ sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E))) ≠ 1}.Finite := by
  intro E _ _ _ hU n γ₀ H₀ _ _ hpos P₁
  obtain ⟨hd0, -⟩ := gramOn_det_totallyPositive_of_posDef H₀ hpos
    (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))
  refine (GlobalTheory.QNorm.finite_valuation_ne_one E (Units.mk0 _ hd0)).subset ?_
  rintro w ⟨hw, hs⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0]
  intro h1
  apply hs
  unfold sgnOn
  have hv : Valued.v (algebraMap E (w.adicCompletion E)
      (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H₀
        (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))).det) = 1 :=
    (w.valuedAdicCompletion_eq_valuation' _).trans h1
  rw [aeval_map_mat, GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq E hU w hw n H₀ (aeval γ₀.val P₁), ordL_eq_zero_of_v_eq_one hv]
  simp

end GlobalTheory.CompanionTheory.FinSign
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteNonsplitSignPlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.finite_nonsplit_sign_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E) (H₀ : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ P₁ : E[X], {w : Pl E | ¬ IsSplitAt w ∧ sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E))) ≠ 1}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.FinSign.main | exact GlobalTheory.CompanionTheory.FinSign.main | (intros; apply GlobalTheory.CompanionTheory.FinSign.main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPolynomialIn

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.FormRatio

theorem exists_eq_mul_aeval (K : Type) [Field K] (σ : K →+* K) (n : ℕ)
    (A H₀ H : Matrix (Fin n) (Fin n) K) (_hA : IsUnit A.det) (hs : A.charpoly.Separable)
    (hH₀ : H₀.det ≠ 0) (e₀ : cT σ A * H₀ * A = H₀) (e : cT σ A * H * A = H) :
    ∃ m : K[X], H = H₀ * aeval A m := by
  have hH₀' : IsUnit H₀.det := isUnit_iff_ne_zero.mpr hH₀
  have hB : IsUnit (cT σ A).det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hH₀ ?_
    have h1 := congrArg Matrix.det e₀
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, zero_mul] at h1
    exact h1.symm
  have k1 : H * A = (cT σ A)⁻¹ * H := by
    calc H * A = ((cT σ A)⁻¹ * cT σ A) * H * A := by
          rw [Matrix.nonsing_inv_mul _ hB, one_mul]
      _ = (cT σ A)⁻¹ * (cT σ A * H * A) := by simp only [mul_assoc]
      _ = (cT σ A)⁻¹ * H := by rw [e]
  have k0 : H₀ * A = (cT σ A)⁻¹ * H₀ := by
    calc H₀ * A = ((cT σ A)⁻¹ * cT σ A) * H₀ * A := by
          rw [Matrix.nonsing_inv_mul _ hB, one_mul]
      _ = (cT σ A)⁻¹ * (cT σ A * H₀ * A) := by simp only [mul_assoc]
      _ = (cT σ A)⁻¹ * H₀ := by rw [e₀]
  have k2 : A * H₀⁻¹ = H₀⁻¹ * (cT σ A)⁻¹ := by
    calc A * H₀⁻¹ = H₀⁻¹ * (H₀ * A) * H₀⁻¹ := by
          rw [← mul_assoc H₀⁻¹ H₀ A, Matrix.nonsing_inv_mul _ hH₀', one_mul]
      _ = H₀⁻¹ * ((cT σ A)⁻¹ * H₀) * H₀⁻¹ := by rw [k0]
      _ = H₀⁻¹ * (cT σ A)⁻¹ * (H₀ * H₀⁻¹) := by simp only [mul_assoc]
      _ = H₀⁻¹ * (cT σ A)⁻¹ := by rw [Matrix.mul_nonsing_inv _ hH₀', mul_one]
  have hc : Commute A (H₀⁻¹ * H) := by
    show A * (H₀⁻¹ * H) = H₀⁻¹ * H * A
    calc A * (H₀⁻¹ * H) = A * H₀⁻¹ * H := (mul_assoc _ _ _).symm
      _ = H₀⁻¹ * (cT σ A)⁻¹ * H := by rw [k2]
      _ = H₀⁻¹ * (H * A) := by rw [k1, mul_assoc]
      _ = H₀⁻¹ * H * A := (mul_assoc _ _ _).symm
  obtain ⟨m, hm⟩ := ClsFin.exists_aeval_of_comm A (H₀⁻¹ * H) hs hc
  refine ⟨m, ?_⟩
  rw [← hm, ← mul_assoc, Matrix.mul_nonsing_inv _ hH₀', one_mul]

end GlobalTheory.CompanionTheory.FormRatio
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPolynomialInStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.hermitian_form_polynomial_in : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (A H₀ H : Matrix (Fin n) (Fin n) K), IsUnit A.det → A.charpoly.Separable → H₀.det ≠ 0 → cT σ A * H₀ * A = H₀ → cT σ A * H * A = H → ∃ m : K[X], H = H₀ * aeval A m := by
  first | exact @GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval | exact GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval | (intros; apply GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMemNormGroup

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.NormClassNorm

theorem norm_mem_normGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k]
    [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r)
    (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k →
    Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈
      GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := by
  intro E _ _ _ k _ _ r Q x hx
  obtain ⟨z, hz⟩ : ∃ z : E, IsCMField.complexConj E z ≠ z := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hθ : IsCMField.complexConj E (z - IsCMField.complexConj E z) =
      -(z - IsCMField.complexConj E z) := by
    rw [map_sub, IsCMField.complexConj_apply_apply]; ring
  obtain ⟨b, B, hB⟩ := GlobalTheory.TraceClasses.exists_bases Q (sub_ne_zero.2 hz.symm) hθ
  have h1 : Isometric Q k (GlobalTheory.TraceClasses.gramRat Q B 1)
      ((1 : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ) : k ⊗[(maximalRealSubfield E)] plus Q) := by
    have := (GlobalTheory.TraceClasses.isometric_tmul_iff Q B k (GlobalTheory.TraceClasses.gramRat Q B 1) 1).2
      (GlobalTheory.HermLocal.CongrOver.of_congr ⟨1, by simp, by simp⟩)
    simpa [Algebra.TensorProduct.one_def] using this
  have h2 := Isometric.of_norm Q k hx h1
  rw [one_mul] at h2
  have h3 := GlobalTheory.TraceClasses.norm_div_mem Q hB k (δ := 1) (by simp) h2
  have h4 : GlobalTheory.QuadSymbol.toUnits (maximalRealSubfield E) k 1 = 1 := map_one _
  rwa [h4, div_one] at h3

end GlobalTheory.CompanionTheory.NormClassNorm

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMemNormGroupStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.norm_mem_norm_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k] [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r) (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k → Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈ GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := by
  first | exact @GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup | exact GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup | (intros; apply GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.FiniteRefSign

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace PositivityTheory.BCUSide.HermitianLocalForms.Lem

theorem ratio_poly : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (A H₀ H : Matrix (Fin n) (Fin n) K), IsUnit A.det → A.charpoly.Separable → H₀.det ≠ 0 → cT σ A * H₀ * A = H₀ → cT σ A * H * A = H → ∃ m : K[X], H = H₀ * aeval A m := GlobalTheory.T.hermitian_form_polynomial_in

theorem sign_rel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ (m : (w.adicCompletion E)[X]) (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → sgnOn (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) = ((GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E (v.adicCompletion (maximalRealSubfield E)) (Units.map (Algebra.norm (v.adicCompletion (maximalRealSubfield E)) : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q →* (v.adicCompletion (maximalRealSubfield E))) x) : ℤ) : ℂ) * sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) := GlobalTheory.T.local_hermitian_class_first

theorem exists_plus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : (w.adicCompletion E)[X], IsHerm (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) → ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m).det ≠ 0 → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m := GlobalTheory.T.local_hermitian_class_second

theorem norms_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E)), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val → (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → x ∈ norms Q (v.adicCompletion (maximalRealSubfield E)) := GlobalTheory.T.local_hermitian_class_third

theorem exists_crt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X], ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := GlobalTheory.T.exists_polynomial_chinese_remainder

theorem herm_of_plus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) := GlobalTheory.T.involution_compatible_polynomial

theorem posDef_of_inf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[(maximalRealSubfield E)] Fld Q)ˣ, (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q u.Completion (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : Fld Q)) → ∀ τ : E →+* ℂ, ∃ Q' : Matrix (Fin n) (Fin n) ℂ, Q'.det ≠ 0 ∧ (H₀ * aeval γ₀.val m).map τ = cT (starRingEnd ℂ) Q' * Q' := GlobalTheory.T.positive_hermitian_polynomial

theorem norm_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k] [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r) (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k → Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈ GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := GlobalTheory.T.norm_mem_norm_group

theorem finite_ref_sign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E) (H₀ : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ P₁ : E[X], {w : Pl E | ¬ IsSplitAt w ∧ sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E))) ≠ 1}.Finite := GlobalTheory.T.finite_nonsplit_sign_places

theorem local_assembly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (t : E[X]), (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ z : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q)ˣ, locPhi hU w hw v hv Q m * ((z : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q (v.adicCompletion (maximalRealSubfield E)) (z : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q)) = locPhi hU w hw v hv Q (atPl w t)) → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val ∧ (H₀ * aeval γ₀.val t).map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) * c.val := by
  intro E _ _ _ hU w hw v hv n γ₀ hP H₀ _ _ h3 m t hz
  exact GlobalTheory.CompanionTheory.LocAssembly.assembly (locJ hU w hw v hv) (locJ_algebraMap hU w hw v hv) (cj w)
    (locJ_cj hU w hw v hv) γ₀ hP H₀ h3 m t hz

end PositivityTheory.BCUSide.HermitianLocalForms.Lem
end
end
