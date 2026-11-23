module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjSelfReciprocalOfDvdEllipticPolynomial
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
public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.ExistsNormSolutionFields
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.GlobalNormOfLocalNorms
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalNormAtSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.TotallyPositiveRealPlaces

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjSelfReciprocalOfDvdEllipticPolynomialStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isConjSelfReciprocal_of_dvd_elliptic_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → ∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ P → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q := by
  first | exact @GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell | exact GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell | (intros; apply GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulPosDef

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryClasses

theorem posDef_cT_inv_mul_inv (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (h : GL (Fin n) E)
    (τ : E →+* ℂ) :
    ((cT (IsCMField.complexConj E).toRingEquiv.toRingHom (h⁻¹).val * (h⁻¹).val).map τ).PosDef := by
  set B : Matrix (Fin n) (Fin n) E := (h⁻¹).val with hB
  have hc : (cT (IsCMField.complexConj E).toRingEquiv.toRingHom B).map τ = (B.map τ)ᴴ := by
    ext i j
    simp [cT, Matrix.conjTranspose_apply, IsCMField.complexEmbedding_complexConj]
  rw [Matrix.map_mul, hc]
  refine Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_)
  have hu : IsUnit B := (h⁻¹).isUnit
  exact hu.map (RingHom.mapMatrix τ)

end GlobalTheory.UnitaryClasses
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.ConjTransposeMulPosDef

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.conj_transpose_mul_posDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (h : GL (Fin n) E) (τ : E →+* ℂ), ((cT (IsCMField.complexConj E).toRingEquiv.toRingHom (h⁻¹).val * (h⁻¹).val).map τ).PosDef := by
  first | exact @GlobalTheory.UnitaryClasses.posDef_cT_inv_mul_inv | (intros; apply GlobalTheory.UnitaryClasses.posDef_cT_inv_mul_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvolutionFixesPolynomialImage

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.NormHasseFixed

theorem cT_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    cT σ (aeval A p) = aeval (cT σ A) (p.map σ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext i j; simp [cT]
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]
    unfold cT
    rw [Matrix.map_smul' _ _ _ (fun x y => map_mul σ x y), Matrix.map_pow, Matrix.transpose_smul, Matrix.transpose_pow]

theorem aeval_mulVec {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} (N : Matrix (Fin n) (Fin n) L)
    (μ : L) (v : Fin n → L) (hv : N *ᵥ v = μ • v) (p : K[X]) : (aeval N p) *ᵥ v = aeval μ p • v := by
  have hpow : ∀ k : ℕ, (N ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, Matrix.smul_mulVec, hpow,
      smul_assoc]

theorem aeval_inv_map_eq {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (γ : GL (Fin n) E)
    (hγ : cT σ γ.val * 1 * γ.val = 1) (m : E[X]) (hm : cT σ (aeval γ.val m) = aeval γ.val m)
    {L : Type} [Field L] [Algebra E L] (α : L) (hα0 : α ≠ 0) (hroot : aeval α γ.val.charpoly = 0) :
    aeval α⁻¹ (m.map σ) = aeval α m := by
  have hU' : cT σ γ.val = (γ⁻¹).val := by
    have h := congrArg (· * (γ⁻¹).val) hγ
    simpa [Matrix.mul_assoc] using h
  rw [aeval_def, ← eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hAv : (γ.val.map (algebraMap E L)) *ᵥ v = α • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hBA : ((γ⁻¹).val.map (algebraMap E L)) * (γ.val.map (algebraMap E L)) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBv : ((γ⁻¹).val.map (algebraMap E L)) *ᵥ v = α⁻¹ • v := by
    have h : ((γ⁻¹).val.map (algebraMap E L)) *ᵥ ((γ.val.map (algebraMap E L)) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    rw [hAv, Matrix.mulVec_smul] at h
    conv_rhs => rw [← h, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  have hmap : ∀ (M : Matrix (Fin n) (Fin n) E) (p : E[X]),
      (aeval M p).map (algebraMap E L) = aeval (M.map (algebraMap E L)) p := by
    intro M p
    have h := aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId E L)) M p
    have e : (⇑(Algebra.ofId E L) : E → L) = algebraMap E L := rfl
    simpa [AlgHom.mapMatrix_apply, e] using h.symm
  have h1 : (cT σ (aeval γ.val m)).map (algebraMap E L) *ᵥ v = (aeval γ.val m).map (algebraMap E L) *ᵥ v := by
    rw [hm]
  rw [cT_aeval, hU', hmap, hmap, aeval_mulVec _ _ v hBv, aeval_mulVec _ _ v hAv] at h1
  exact smul_left_injective L hv0 h1


open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField in
theorem invol_mk_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], cT (IsCMField.complexConj E).toRingEquiv.toRingHom (aeval γ.val m) = aeval γ.val m → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  intro E _ _ _ n γ hγ _ m hm r Q hQ
  have hγ' : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val * 1 * γ.val = 1 := hγ
  have hroot : aeval (AdjoinRoot.root Q.1) γ.val.charpoly = 0 := by
    obtain ⟨c, hc⟩ := hQ
    rw [hc, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  have h := aeval_inv_map_eq (IsCMField.complexConj E).toRingEquiv.toRingHom γ hγ' m hm (AdjoinRoot.root Q.1) (root_ne_zero Q) hroot
  rw [aeval_def, eval₂_map, AdjoinRoot.aeval_eq] at h
  refine Eq.trans ?_ h
  show AdjoinRoot.lift ((AdjoinRoot.of Q.1).comp (IsCMField.complexConj E : E →+* E)) (AdjoinRoot.root Q.1)⁻¹
    (eval₂_conj_inv_root Q) (AdjoinRoot.mk Q.1 m) = _
  rw [AdjoinRoot.lift_mk]
  rfl

end GlobalTheory.NormHasseFixed
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.InvolutionFixesPolynomialImage

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.involution_fixes_polynomial_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], cT (IsCMField.complexConj E).toRingEquiv.toRingHom (aeval γ.val m) = aeval γ.val m → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  first | exact @GlobalTheory.NormHasseFixed.invol_mk_eq | (intros; apply GlobalTheory.NormHasseFixed.invol_mk_eq <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NonsplitCentraliserNormElement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.nonsplit_centraliser_norm_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = (aeval γ.val m).map (algebraMap E (w.adicCompletion E))) → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∀ w w' : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v → w'.under (𝓞 (maximalRealSubfield E)) = v → w = w') → ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  first | exact @GlobalTheory.NormInert.main | exact GlobalTheory.NormInert.main | (intros; apply GlobalTheory.NormInert.main <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NonsplitPlaceNormCentraliser

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormHasseCent

theorem inv_hh {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (k : GL (Fin n) K) : (k.val * cT σ k.val)⁻¹ = cT σ (k⁻¹).val * (k⁻¹).val :=
  Matrix.inv_eq_right_inv (by rw [Matrix.mul_assoc, cT_units_left', Units.mul_inv])

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := by
  intro E _ _ _ hU n γ h hγ hP hconj hloc
  set σ := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσdef
  have hσ : ∀ x, σ (σ x) = x := fun x => IsCMField.complexConj_apply_apply E x
  set N := cT σ (h⁻¹).val * (h⁻¹).val with hN
  have hγ' : cT σ γ.val * 1 * γ.val = 1 := hγ
  have hinv := inv_of_unit σ h γ hconj
  have hγγ : γ.val * cT σ γ.val = 1 := by
    rw [Matrix.mul_one] at hγ'; exact mul_eq_one_comm.1 hγ'
  have hcomm : γ.val * N = N * γ.val := by
    have := congrArg (γ.val * ·) hinv
    simp only [← Matrix.mul_assoc, hγγ, Matrix.one_mul] at this
    rw [hN]; simpa only [Matrix.mul_assoc] using this.symm
  obtain ⟨m, hm⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ.val N hP.2.2.1 hcomm
  have hherm : cT σ (aeval γ.val m) = aeval γ.val m := by
    rw [← hm]; exact herm_of σ hσ h
  have hM : (h.val * cT σ h.val)⁻¹ = aeval γ.val m := by rw [inv_hh, ← hN, hm]
  have hsr := GlobalTheory.T.isConjSelfReciprocal_of_dvd_elliptic_polynomial E n _ hP
  have hfix := GlobalTheory.T.involution_fixes_polynomial_image E n γ hγ hP m hherm
  have hloc' : ∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = (aeval γ.val m).map (algebraMap E (w.adicCompletion E)) := (fun w hw => by
    obtain ⟨c, hc1, hc2⟩ := hloc w hw
    refine ⟨c, hc1, ?_⟩
    rw [hc2, inv_hh, ← hm, hN, ← map_inv]
    rw [Matrix.map_mul, cT_map hU w hw]; rfl)
  have hfin : ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
    intro r Q hQ hx v
    by_cases hs : ∃ w w' : Pl E, w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧ w'.under (𝓞 (maximalRealSubfield E)) = v
    · exact GlobalTheory.T.local_norm_at_split_place E r Q _ hx v hs
    · refine GlobalTheory.T.nonsplit_centraliser_norm_element E hU n γ hγ hP m hloc' r Q hQ hx v (fun w w' hw hw' => ?_)
      by_contra hne
      exact hs ⟨w, w', hne, hw, hw'⟩
  have hinf := GlobalTheory.T.totally_positive_real_places E n γ hγ hP m (fun τ => by rw [← hm]; exact GlobalTheory.T.conj_transpose_mul_posDef E n h τ)
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_norm_solution_fields E n γ hγ hP hsr m (fun r Q hQ =>
    GlobalTheory.T.global_norm_of_local_norms E r Q _ (hfix r Q hQ) (hfin r Q hQ (hfix r Q hQ)) (hinf r Q hQ (hfix r Q hQ)))
  exact ⟨c, hc1, by rw [hc2, hM]⟩

end GlobalTheory.NormHasseCent
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NonsplitPlaceNormCentraliserStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.nonsplit_place_norm_centraliser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := by
  first | exact @GlobalTheory.NormHasseCent.main | (intros; apply GlobalTheory.NormHasseCent.main <;> assumption)
end
end
