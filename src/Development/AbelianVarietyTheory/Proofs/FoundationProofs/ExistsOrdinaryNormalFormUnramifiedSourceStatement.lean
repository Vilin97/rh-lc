module

public import Development.AbelianVarietyTheory.Definitions.Foundations.VanishOrdL
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterPowPredEqOneOfKillsPrimeRootsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoefficientRingFiniteExtensionPadicStatement
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUpperTriangularConjIntegralCompactStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TargetAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedOfLevelAwayInertiaCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Connected.Separation

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNf

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.NfEx

theorem up2 {k : Type} [Field k] (X Y Z : Matrix (Fin 2) (Fin 2) k) (hX : X 1 0 = 0) (hY : Y 1 0 = 0) (hZ : Z 1 0 = 0) :
    (X * Y * Z) 1 0 = 0 ∧ (X * Y * Z) 0 0 = X 0 0 * Y 0 0 * Z 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hX, hY, hZ]

theorem inv_up {k : Type} [Field k] (B : GL (Fin 2) k) (hB : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 ∧
    (B : Matrix (Fin 2) (Fin 2) k) 0 0 * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
  have key : ∀ i j, ∑ x, (B : Matrix (Fin 2) (Fin 2) k) i x * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) x j =
      (1 : Matrix (Fin 2) (Fin 2) k) i j := fun i j => by
    rw [← Matrix.mul_apply, B.mul_inv]
  have e10 := key 1 0
  have e11 := key 1 1
  have e00 := key 0 0
  rw [Fin.sum_univ_two, hB, zero_mul, zero_add] at e10 e11
  rw [Fin.sum_univ_two] at e00
  rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e10
  rw [Matrix.one_apply_eq] at e11 e00
  have hN : ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    rcases mul_eq_zero.1 e10 with h | h
    · rw [h, zero_mul] at e11
      exact absurd e11 zero_ne_one
    · exact h
  refine ⟨hN, ?_⟩
  rw [hN, mul_zero, add_zero] at e00
  exact e00

end GlobalTheory.NfEx

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleRestrictionOfIso

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.IrrConj

theorem isIrrSub_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ}
    (H H' : Subgroup Γ) (hH : ∀ s, s ∈ H → s ∈ H')
    (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k) (hg : ∀ s, r' s = g * r s * g⁻¹)
    (hr : IsIrrSub (r.comp H.subtype) ⊤) : IsIrrSub (r'.comp H'.subtype) ⊤ := by
  first
  | exact @_root_.GlobalTheory.ConjugateIrreducibility.target
  | exact _root_.GlobalTheory.ConjugateIrreducibility.target
  | (apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateIrreducibility.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateIrreducibility.target ..)

theorem dt_eq_of_repIso {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
    (W W' : R2 Ω l) (g : GL (Fin 2) (Qbar l)) (hg : ∀ s, W' s = g * W s * g⁻¹) (s : G ℚ Ω) :
    dt W' s = dt W s := by
  simp only [dt, MonoidHom.comp_apply, hg s, map_mul, map_inv]
  rw [mul_comm (Matrix.GeneralLinearGroup.det g), mul_assoc, mul_inv_cancel, mul_one]

theorem irr_of_repIso : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (W W' : R2 Ω l),
    RepIso W W' → IsIrr (W.comp (H0g W).subtype) → IsIrr (W'.comp (H0g W').subtype) := by
  intro Ω _ _ l _ W W' ⟨g, hg⟩ h
  refine isIrrSub_conj (H0g W) (H0g W') ?_ W W' g hg h
  intro s hs
  simp only [H0g, Subgroup.mem_inf, MonoidHom.mem_ker] at hs ⊢
  exact ⟨hs.1, by rw [dt_eq_of_repIso W W' g hg]; exact hs.2⟩

end GlobalTheory.IrrConj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleRestrictionOfIsoStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.irreducible_restriction_of_iso : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (W W' : R2 Ω l), RepIso W W' → IsIrr (W.comp (H0g W).subtype) → IsIrr (W'.comp (H0g W').subtype) := by
  first | exact @GlobalTheory.IrrConj.irr_of_repIso | exact GlobalTheory.IrrConj.irr_of_repIso | (intros; apply GlobalTheory.IrrConj.irr_of_repIso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SrcOfRepIso

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SrcConj

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

theorem tw_conj (r r' : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (g : GL (Fin n) k)
    (h : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) : tw r' χ s = g * tw r χ s * g⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, tw_val, tw_val, h s, Units.val_mul, Units.val_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem isSSRep_conj (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k) (h : ∀ s, r' s = g * r s * g⁻¹)
    (hr : IsSSRep r) : IsSSRep r' := by
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ?_ ?_ hr
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · intro s
    rw [h s, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group

theorem att_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k' : ℕ}
    (f : Newform k') (V V' : G ℚ Ω →* GL (Fin 2) (Qbar l)) (g : GL (Fin 2) (Qbar l))
    (h : ∀ s, V' s = g * V s * g⁻¹) (hV : f.Att ι V) : f.Att ι V' := by
  refine ⟨isSSRep_conj V V' g h hV.1, hV.2.mono fun w hw A hA => ?_⟩
  obtain ⟨hI, hF⟩ := hw A hA
  refine ⟨fun s hs => by rw [h s, hI s hs, mul_one, mul_inv_cancel], fun σ hσ => ?_⟩
  rw [← hF σ hσ, h σ⁻¹, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end GlobalTheory.Ord2.SrcConj

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrdinaryNormalFormUnramifiedSource

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.NfSrc

theorem upper_triangular_conj_lower_right_entry_eq {k : Type} [Field k] (B : GL (Fin 2) k) (X : Matrix (Fin 2) (Fin 2) k)
    (hB : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (hX : X 1 0 = 0) :
    ((B : Matrix (Fin 2) (Fin 2) k) * X * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 1 = X 1 1 := by
  have hinv := GlobalTheory.NfEx.inv_up B hB
  have h1 : ((B⁻¹ * B : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by simp
  have a11 := congrFun (congrFun h1 1) 1
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv.1, zero_mul, zero_add, Matrix.one_apply_eq] at a11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hB, hX, zero_mul, zero_add, mul_zero]
  calc _ = X 1 1 * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 1 * (B : Matrix (Fin 2) (Fin 2) k) 1 1 := by ring
    _ = _ := by rw [mul_assoc, a11, mul_one]

end GlobalTheory.NfSrc

theorem GlobalTheory.Ord2.exists_nf_srcUr : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → SrcL ι e W → ∃ (S : Finset Pl) (A : ValuationSubring Ω) (W' : R2 Ω l) (g : Newform (2 * e + 1)), RepIso W W' ∧ Nf e S A W' ∧ SrcUr ι e A W' g := by
  intro l _ Ω _ _ _ ι e W hl he hW hS
  obtain ⟨⟨g0, χ, A, κ, hM0, ha0, hχ, hatt, hA, hfl, hin⟩, hne⟩ := hS
  obtain ⟨g, hg⟩ := hfl
  obtain ⟨M, hM, hMa⟩ := hW.away
  obtain ⟨S, hSa, hSu⟩ := GlobalTheory.T.unramified_of_levelAway_inertia_characters l Ω W M hM hMa
  let r : G ℚ Ω →* GL (Fin 2) (Qbar l) := (MulAut.conj g).toMonoidHom.comp W
  have hrc : Continuous r := by
    show Continuous fun s => g * W s * g⁻¹
    exact (continuous_const.mul hW.cont).mul continuous_const
  obtain ⟨E, hE, hEm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l (G ℚ Ω) 2 r
    (fun i j => ((Units.continuous_val.comp hrc).matrix_elem i j))
  obtain ⟨B, hB10, hBint⟩ := GlobalTheory.T.exists_upperTriangular_conj_integral_compact l (G ℚ Ω) E r hE hrc hEm
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_coefficientRing_finiteExtension_padic l E hE
  let h : GL (Fin 2) (Qbar l) := B * g
  let W' : R2 Ω l := (MulAut.conj h).toMonoidHom.comp W
  have hh : ∀ s, W' s = h * W s * h⁻¹ := fun s => rfl
  have hW' : ∀ s, W' s = B * r s * B⁻¹ := fun s => by
    show h * W s * h⁻¹ = B * (g * W s * g⁻¹) * B⁻¹
    simp only [h, mul_inv_rev]; group
  have hiso : RepIso W W' := ⟨h, hh⟩
  have hdt : dt W' = dt W := by
    ext s
    rw [GlobalTheory.Ord2.TwDet.dt_coe, GlobalTheory.Ord2.TwDet.dt_conj W h s]
    rfl
  have hdet : ∀ s, (dt W' s : Qbar l) = (mat W' s).det := fun s => rfl
  have hker : ∀ s, W' s = 1 ↔ W s = 1 := fun s => by
    show h * W s * h⁻¹ = 1 ↔ W s = 1
    constructor
    · intro hh; rw [mul_inv_eq_one, mul_eq_left] at hh; exact hh
    · intro hh; rw [hh]; simp
  have hinv := GlobalTheory.NfEx.inv_up B hB10
  have hup : ∀ (s : G ℚ Ω) (hs : s ∈ Dec (F := ℚ) A), mat W' s 1 0 = 0 ∧ mat W' s 0 0 = (κ 0 ⟨s, hs⟩ : Qbar l) ∧
      mat W' s 1 1 = (κ 1 ⟨s, hs⟩ : Qbar l) := by
    intro s hs
    have h1 := (hg ⟨s, hs⟩).1 1 0 (by decide)
    have h2 := (hg ⟨s, hs⟩).2 0
    have h3 := (hg ⟨s, hs⟩).2 1
    have := GlobalTheory.NfEx.up2 (B : Matrix (Fin 2) (Fin 2) (Qbar l)) ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))
      ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1 hinv.1
    have e1 : mat W' s = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      simp only [mat, hW', Units.val_mul]
    refine ⟨by rw [e1]; exact this.1, ?_, ?_⟩
    · rw [e1, this.2, ← h2]
      change _ = ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0
      calc _ = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 := by ring
        _ = _ := by rw [hinv.2, one_mul]
    · rw [e1, GlobalTheory.NfSrc.upper_triangular_conj_lower_right_entry_eq B ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1]
      exact h3

  have hline : ∀ (s : G ℚ Ω) (hs : s ∈ Ine (F := ℚ) A),
      mat W' s 0 0 = eps l s ^ e * (χ s : Qbar l) := by
    intro s hs
    have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
    obtain ⟨u10, u00, u11⟩ := hup s hd
    have hi := hin ⟨s, hd⟩ hs
    have hD : (dt W s : Qbar l) = mat W' s 0 0 * mat W' s 1 1 := by
      rw [← hdt, hdet, Matrix.det_fin_two, u10, mul_zero, sub_zero]
    have hdne : (dt W s : Qbar l) ≠ 0 := Units.ne_zero _
    simp only [zpow_natCast] at hi
    rw [← u11] at hi
    simp only [eps]
    calc mat W' s 0 0 = mat W' s 0 0 * (mat W' s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ e * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l))) := by
          rw [hi, mul_one]
      _ = (mat W' s 0 0 * mat W' s 1 1) * (dt W s : Qbar l)⁻¹ * ((cycBar ℚ Ω l s : Qbar l) ^ e * (χ s : Qbar l)) := by ring
      _ = _ := by rw [← hD, mul_inv_cancel₀ hdne, one_mul]
  refine ⟨S, A, W', g0, hiso, ?_, ?_⟩
  · refine
      { l_odd := hl
        e_pos := he
        cont := ?_
        int := ⟨c, fun s i j => (hc _).2 ⟨?_, ?_⟩⟩
        above := hSa
        unr := ?_
        det2 := by rw [hdt]; exact hW.det2
        odd := by rw [hdt]; exact hW.odd
        irr := GlobalTheory.T.irreducible_restriction_of_iso Ω l W W' hiso hW.irr
        atL := hA
        upper := fun s hs => (hup s hs).1
        wt := ?_
        ne := ?_ }
    · show Continuous fun s => h * W s * h⁻¹
      exact (continuous_const.mul hW.cont).mul continuous_const
    · have := (hBint s i j).1; simpa only [mat, hW'] using this
    · have := (hBint s i j).2; simpa only [mat, hW'] using this
    · intro w hw B' hB' s hs
      exact (hker s).2 (hSu w hw B' hB' hs)
    · refine ⟨l - 1, ?_, fun s hs => ?_⟩
      · have := (Fact.out : l.Prime).two_le; omega
      · rw [hline s hs, mul_pow, ← pow_mul]
        have hχ1 := GlobalTheory.T.character_pow_pred_eq_one_of_killsPrimeRoots Ω l _ χ s hχ
        rw [← Units.val_pow_eq_pow_val (χ s), hχ1, Units.val_one, mul_one]
    · obtain ⟨s, hs⟩ := hne A κ hA ⟨g, hg⟩
      refine ⟨s, s.2, ?_⟩
      rw [(hup s s.2).2.1]
      intro hh
      exact hs (Units.ext hh)
  · refine ⟨hM0, ha0, χ, hχ, ?_, ?_⟩
    · rw [hdt]
      exact SrcConj.att_conj ι g0 _ _ h (SrcConj.tw_conj W W' _ h hh) hatt
    · intro s hs
      have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
      rw [(hup s hd).2.2, hdt]
      exact hin ⟨s, hd⟩ hs

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrdinaryNormalFormUnramifiedSourceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_ordinary_normal_form_unramified_source : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → SrcL ι e W → ∃ (S : Finset Pl) (A : ValuationSubring Ω) (W' : R2 Ω l) (g : Newform (2 * e + 1)), RepIso W W' ∧ Nf e S A W' ∧ SrcUr ι e A W' g := by
  first | exact @GlobalTheory.Ord2.exists_nf_srcUr | exact GlobalTheory.Ord2.exists_nf_srcUr | (intros; apply GlobalTheory.Ord2.exists_nf_srcUr <;> assumption)
end
end
