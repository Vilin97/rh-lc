module

public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemIntegralPointsOfLatticeStabilizerStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemUnitaryGroupAntidiagonalFormStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorCompSphericalConvolution

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalSurjectiveFromTrivOutside

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertSurj

theorem exists_supported (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (m : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ∃ z : AL L, compAt L v z = m ∧ ∀ u, u ≠ v → compAt L u z = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨a, c, h⟩ := GlobalTheory.InertUmax.tensor_decomp b m
  refine ⟨b 0 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v a +
    b 1 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩
  · rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same,
      GlobalTheory.InertUmax.sgl_same, h]
  · intro u hu
    rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu,
      GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L) :
    compAt L u (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (u.adicCompletion (maximalRealSubfield L)) (compAt L u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [GlobalTheory.InertUmax.compAt_tmul]
    simp [conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, GlobalTheory.InertUmax.compAt_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem loc_surj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (y : GL (Fin n) (w.adicCompletion L)), y ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  intro L _ _ _ n v w Dv y hy
  classical
  let sig := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
  let eS : w.adicCompletion L →+* L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) :=
    Dv.e.symm.toRingHom
  have hcomm : ∀ a, sig (eS a) = eS (Dv.σw a) := by
    intro a
    apply Dv.e.injective
    have h := Dv.comm (eS a)
    simp only [eS, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h ⊢
    exact h
  let Pm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : Matrix (Fin n) (Fin n) _)
  let Qm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Dv.P⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)
  let Ym : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (y : Matrix (Fin n) (Fin n) _)
  have hPQ : Pm * Qm = 1 := by simp [Pm, Qm]
  have hy' : Formalism.UG.cT Dv.σw Ym * Formalism.UG.antiJ (w.adicCompletion L) n * Ym =
      Formalism.UG.antiJ (w.adicCompletion L) n := hy
  let X := Pm * Ym * Qm
  have hX : Formalism.UG.cT Dv.σw X * X = 1 := by
    have hP := Dv.Panti
    change Formalism.UG.cT Dv.σw Pm * Pm = _ at hP
    calc Formalism.UG.cT Dv.σw X * X
        = Formalism.UG.cT Dv.σw Qm * (Formalism.UG.cT Dv.σw Ym * (Formalism.UG.cT Dv.σw Pm * Pm) * Ym) * Qm := by
          simp only [X, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT Dv.σw Qm * (Formalism.UG.cT Dv.σw Pm * Pm) * Qm := by rw [hP, hy']
      _ = Formalism.UG.cT Dv.σw (Pm * Qm) * (Pm * Qm) := by
          simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul]
  have hX' : X * Formalism.UG.cT Dv.σw X = 1 := mul_eq_one_comm.mp hX
  let M := X.map eS
  have hMc : conjT sig M = (Formalism.UG.cT Dv.σw X).map eS := by
    ext i j
    simp [M, conjT, Formalism.UG.cT, hcomm]
  have hM : M * conjT sig M = 1 := by
    rw [hMc]
    change X.map eS * (Formalism.UG.cT Dv.σw X).map eS = 1
    rw [← Matrix.map_mul, hX', Matrix.map_one _ (map_zero _) (map_one _)]
  choose lift hlv hlw using GlobalTheory.InertSurj.exists_supported L v
  let E : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v 1
  have hEv : compAt L v E = 1 := by
    rw [GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]; rfl
  have hEw : ∀ u, u ≠ v → compAt L u E = 0 := by
    intro u hu
    rw [GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v 1 hu, tmul_zero]
  let Z : Matrix (Fin n) (Fin n) (AL L) := M.map lift + (1 - E) • (1 : Matrix (Fin n) (Fin n) (AL L))
  have hZv : Z.map (compAt L v) = M := by
    ext i j
    simp only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_sub, map_one, hEv, hlv, sub_self, zero_mul, add_zero]
  have hZw : ∀ u, u ≠ v → Z.map (compAt L u) = 1 := by
    intro u hu
    ext i j
    simp only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_sub, map_one, hEw u hu, hlw _ u hu, sub_zero, one_mul, zero_add]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hZconj : ∀ u, (conjT (conjAL L) Z).map (compAt L u) =
      conjT (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (u.adicCompletion (maximalRealSubfield L)))
        (Z.map (compAt L u)) := by
    intro u
    ext i j
    simp [conjT, GlobalTheory.InertSurj.compAt_conjAL]
  have hZZ : Z * conjT (conjAL L) Z = 1 := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.InertUmax.eq_zero_of_compAt
    intro u
    have key : (Z * conjT (conjAL L) Z).map (compAt L u) = 1 := by
      rw [Matrix.map_mul, hZconj]
      rcases eq_or_ne u v with rfl | hu
      · rw [hZv]; exact hM
      · rw [hZw u hu, conjT_one, Matrix.one_mul]
    have h1 := congrFun (congrFun key i) j
    have h2 := congrFun (congrFun (Matrix.map_one (compAt L u) (map_zero _) (map_one _)) i) j
    simp only [Matrix.map_apply] at h1 h2
    rw [map_sub, h1, h2, sub_self]
  have hZZ' : conjT (conjAL L) Z * Z = 1 := mul_eq_one_comm.mp hZZ
  let g : GL (Fin n) (AL L) := ⟨Z, conjT (conjAL L) Z, hZZ, hZZ'⟩
  have hg : g ∈ ReciprocityTheory.Aut.GA L n := hZZ
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · intro u hu
    exact hZw u (by simpa using hu)
  · have hb : Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) (((⟨g, hg⟩ : GAf L n)) : GL (Fin n) (AL L))) =
        Dv.P * y * Dv.P⁻¹ := by
      apply Units.ext
      change (Z.map (compAt L v)).map _ = X
      rw [hZv]
      ext i j
      simp [M, eS]
    unfold InertDatum.loc
    rw [hb]
    group

end GlobalTheory.InertSurj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalSurjectiveFromTrivOutsideStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inertLocal_surjective_from_trivOutside : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (y : GL (Fin n) (w.adicCompletion L)), y ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  first | exact @GlobalTheory.InertSurj.loc_surj | exact GlobalTheory.InertSurj.loc_surj | (intros; apply GlobalTheory.InertSurj.loc_surj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorConvolutionEqComp

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open GlobalTheory.SatInd

namespace GlobalTheory.InertConvMul

theorem eq_of_coset {G : Type} [Group G] {K : Subgroup G} {k : Type} {H : G → k}
    (hH : ∀ (a : G) (c : K), H (a * c) = H a) {a b : G} (hab : (a : G ⧸ K) = b) : H a = H b := by
  have hc := QuotientGroup.eq.1 hab
  have := hH a ⟨a⁻¹ * b, hc⟩
  change H (a * (a⁻¹ * b)) = H a at this
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem finsum_eq_of_support_subset_range {α β M : Type} [AddCommMonoid M] {F : α → M} {e : β → α}
    (he : Function.Injective e) (hs : Function.support F ⊆ Set.range e) :
    ∑ᶠ c, F c = ∑ᶠ d, F (e d) := by
  rw [← finsum_mem_range he, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs, finsum_mem_support]

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem conv_of (Dv : InertDatum L n v w) (U : Subgroup (GAf L n))
    (hU : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n))
    (hA : ∀ x : GAf L n, Dv.loc x ∈ GU Dv.σw n)
    (hK : ∀ u ∈ Umax L n, (⟨Dv.loc u, hA u⟩ : GU Dv.σw n) ∈ KU Dv.σw n)
    (hC : ∀ y ∈ GU Dv.σw n, ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y)
    (W : Type) [AddCommGroup W] [Module ℂ W]
    (h : GU Dv.σw n → ℂ) (hh : h ∈ Hecke ℂ (KU Dv.σw n))
    (h' : GU Dv.σw n → ℂ) (hh' : h' ∈ Hecke ℂ (KU Dv.σw n))
    (f : GAf L n → W) (hf : ∀ κ ∈ U, NG.rt L n κ f = f) :
    heckeFunI L n U Dv (conv (KU Dv.σw n) h h') f =
      heckeFunI L n U Dv h (heckeFunI L n U Dv h' f) := by
  exact GlobalTheory.InertConv.conv_of Dv U hU hA
    (fun u hu i j => GlobalTheory.SatInd.CosetFin.entries_int (hK u hu) i j)
    hC W h hh h' hh' f hf

theorem heckeFunI_conv_mul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.conv (Formalism.UG.KU Dv.σw n) h₁ h₂) f = heckeFunI L n U Dv h₁ (heckeFunI L n U Dv h₂ f) := by
  intro L _ _ _ n v w Dv U hU W _ _ h₁ h₂ hh₁ hh₂ f hf
  exact conv_of Dv U hU (GlobalTheory.T.inertLocal_mem_unitaryGroup_antidiagonalForm L n v w Dv)
    (fun u hu => GlobalTheory.T.inertLocal_mem_integralPoints_of_latticeStabilizer L n v w Dv u hu _) (GlobalTheory.T.inertLocal_surjective_from_trivOutside L n v w Dv) W h₁ hh₁ h₂ hh₂ f hf

end GlobalTheory.InertConvMul
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorConvolutionEqCompStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inertHeckeOperator_convolution_eq_comp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.conv (Formalism.UG.KU Dv.σw n) h₁ h₂) f = heckeFunI L n U Dv h₁ (heckeFunI L n U Dv h₂ f) := by
  first | exact @GlobalTheory.InertConvMul.heckeFunI_conv_mul | exact GlobalTheory.InertConvMul.heckeFunI_conv_mul | (intros; apply GlobalTheory.InertConvMul.heckeFunI_conv_mul <;> assumption)
end
end
