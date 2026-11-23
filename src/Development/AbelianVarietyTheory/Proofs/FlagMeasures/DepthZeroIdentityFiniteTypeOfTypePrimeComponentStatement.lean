module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIndependentSubfamilySameISupStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPadicLiftMulPrincipalCongruenceOfReductionStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteTypeEqISupSplitTrivialTranslatesLocalStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTrivialTranslateLocalComponentDisjointOrLeStatement
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ValuationLtOneIffNormLtOnePadicCmCompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmSplitPlaceEqOfPrimeEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitUniqSer

theorem splitPlace_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L),
    s.w = s'.w → s = s' :=
  GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq

end GlobalTheory.SplitUniqSer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmSplitPlaceEqOfPrimeEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.cmSplitPlace_eq_of_prime_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L), s.w = s'.w → s = s' := by
  first | exact @GlobalTheory.SplitUniqSer.splitPlace_unique | exact GlobalTheory.SplitUniqSer.splitPlace_unique | (intros; apply GlobalTheory.SplitUniqSer.splitPlace_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrincipalCongruenceMapCompletionSubOneValuedLt

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem GLp.inc_map_sub_one_valued_lt_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, ‖θ z‖ < 1 → Valued.v z < 1) → ∀ k ∈ (GlobalTheory.GLp.red g n).ker, ∀ a b : Fin n, Valued.v ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (((((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1 := by
  intro F _ _ v g n _ θ hθ k hk a b
  have hk' : PadicInt.toZMod ((k : Matrix (Fin n) (Fin n) ℤ_[g]) a b) =
      ((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b := by
    have := congrArg (fun x : GL (Fin n) (ZMod g) => (x : Matrix (Fin n) (Fin n) (ZMod g)) a b)
      (MonoidHom.mem_ker.mp hk)
    simpa [GlobalTheory.GLp.red] using this
  set c : ℕ := (((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val with hc
  have hmem : (k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
    rw [RingHom.mem_ker, map_sub, hk', map_natCast, hc, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod] at hmem
  have hnorm : ‖(k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g])‖ < 1 := PadicInt.mem_nonunits.mp hmem
  apply hθ
  have he : θ ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (c : v.adicCompletion F)) =
      (((k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) : ℤ_[g]) : ℚ_[g]) := by
    simp [GlobalTheory.GLp.inc, Matrix.GeneralLinearGroup.map]
  rw [he, PadicInt.padic_norm_e_of_padicInt]
  exact hnorm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrincipalCongruenceMapCompletionSubOneValuedLtStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.principalCongruence_map_completion_sub_one_valued_lt : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, ‖θ z‖ < 1 → Valued.v z < 1) → ∀ k ∈ (GlobalTheory.GLp.red g n).ker, ∀ a b : Fin n, Valued.v ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (((((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1 := by
  first | exact @GlobalTheory.GLp.inc_map_sub_one_valued_lt_one | exact GlobalTheory.GLp.inc_map_sub_one_valued_lt_one | (intros; apply GlobalTheory.GLp.inc_map_sub_one_valued_lt_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ValuationLtOneIffNormLtOnePadicCmCompletionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.valuation_lt_one_iff_norm_lt_one_padic_cmCompletion : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (g : ℕ) [Fact g.Prime] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (j : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i → Continuous j → ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z < 1 ↔ ‖j.symm (i z)‖ < 1 := by
  first | exact @GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous | exact GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous | (intros; apply GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DepthZeroIdentityFiniteTypeOfTypePrimeComponent

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

noncomputable section

open GlobalTheory.LabPin

namespace GlobalTheory.DepthZeroSer

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem rt_rt' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (h h' : GAf L n) (f : GAf L n → ℂ) :
    NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
  funext x; simp [NG.rt, mul_assoc]

theorem rt_one' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (f : GAf L n → ℂ) :
    NG.rt L n 1 f = f := by
  funext x; simp [NG.rt]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : GlobalTheory.SmGL.IrrRep G) : Nontrivial τ.V := by
  haveI := τ.irr
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  ext x
  simp [Subsingleton.elim x 0]

theorem serFix_of_locS {L : Type} [Field L] [NumberField L] [IsCMField L] {n g : ℕ} [Fact g.Prime]
    (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (j : ℚ_[g] ≃+* s.w.adicCompletion L) (hj : Continuous j) (a : MonoidAlgebra ℂ (GL (Fin n) (ZMod g)))
    (hloc : GlobalTheory.HeightCounting.IsLocS π.S s τ)
    (ha : ∀ y ∈ GlobalTheory.GLp.fixK1 (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)),
      GlobalTheory.GLp.actK (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)) a y = y) :
    SerFix π s a := by
  classical
  obtain ⟨i, T, hi, -, hT, hTS, hTeq⟩ := hloc
  set ρ' := τ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) j.toRingHom) with hρ'
  set θ : s.v.adicCompletion (maximalRealSubfield L) ≃+* ℚ_[g] := i.trans j.symm with hθdef
  have hθ : ∀ z, Valued.v z < 1 ↔ ‖θ z‖ < 1 := fun z => GlobalTheory.T.valuation_lt_one_iff_norm_lt_one_padic_cmCompletion L s g i j hi hj z
  have hτθ : ∀ A : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom A) = ρ' (Matrix.GeneralLinearGroup.map θ.toRingHom A) := by
    intro A
    simp only [hρ', MonoidHom.coe_comp, Function.comp_apply]
    congr 1
    ext a b
    simp [θ]
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  haveI := nontrivial_of_irr τ
  intro ℓ hℓ φ hφS hφfix
  let N : {y : GAf L n // TrivOutside {s.v}ᶜ y} → Submodule ℂ (GAf L n → ℂ) :=
    fun y => LinearMap.range ((NG.rt L n y.1).comp T)
  have hspan := GlobalTheory.T.finiteType_eq_iSup_splitTrivial_translates_local L n π s τ.V T hT hTS (fun x hx a => ⟨_, (hTeq x hx a).symm⟩)
  have hNst : ∀ y x, TrivOutside {s.v} x → ∀ f ∈ N y, NG.rt L n x f ∈ N y := by
    rintro y x hx f ⟨b, rfl⟩
    refine ⟨τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) b, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hTeq x hx b, rt_rt', rt_rt', (hI.2.1 x y.1 hx y.2).eq]
  have hsupst : ∀ (J : Finset _) x, TrivOutside {s.v} x → ∀ f ∈ ⨆ j ∈ J, N j, NG.rt L n x f ∈ ⨆ j ∈ J, N j := by
    intro J x hx f hf
    have : (⨆ j ∈ J, N j) ≤ (⨆ j ∈ J, N j).comap (NG.rt L n x) := by
      refine iSup₂_le fun j hj => ?_
      intro f hf
      exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hNst j x hx f hf))
    exact this hf
  have hdich : ∀ y (J : Finset _), Disjoint (N y) (⨆ j ∈ J, N j) ∨ N y ≤ ⨆ j ∈ J, N j :=
    fun y J => GlobalTheory.T.splitTrivialTranslate_localComponent_disjoint_or_le L n s τ i T hT hTeq y.1 y.2 _ (hsupst J)
  have hφ : φ ∈ ⨆ y, N y := hspan ▸ hφS
  obtain ⟨F, hF⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  obtain ⟨J, -, hJsup, hJuniq⟩ := GlobalTheory.T.exists_independent_subfamily_same_iSup _ _ N hdich F
  rw [← hJsup] at hF
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum N φ).1 hF
  choose c hc using fun y => (μ y).2
  have hφsum : φ = ∑ y ∈ J, NG.rt L n y.1 (T (c y)) := by
    rw [← hμ]; exact Finset.sum_congr rfl fun y _ => (hc y).symm
  have hinj : ∀ (y : {y : GAf L n // TrivOutside {s.v}ᶜ y}), Function.Injective (fun b => NG.rt L n y.1 (T b)) := by
    intro y b b' h
    apply hT
    have := congrArg (NG.rt L n y.1⁻¹) h
    simpa [rt_rt', rt_one'] using this
  have hfix : ∀ y ∈ J, c y ∈ GlobalTheory.GLp.fixK1 ρ' := by
    intro y hy
    simp only [GlobalTheory.GLp.fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro kk
    obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := hI.2.2 (Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n kk))
    have hlift : IsLift s x (1 : GL (Fin n) (ZMod g)) :=
      ⟨hx1, fun p q => by
        have H := GlobalTheory.T.principalCongruence_map_completion_sub_one_valued_lt _ s.v g n θ (fun z => (hθ z).2) (kk : GL (Fin n) ℤ_[g]) kk.2 p q
        rw [hx2]
        exact H⟩
    have hx := hφfix x hlift
    have hθx : Matrix.GeneralLinearGroup.map θ.toRingHom (s.loc n x) = GlobalTheory.GLp.inc g n kk := by
      rw [hx2]; ext; simp

    rw [hφsum, map_sum] at hx
    have hx' : ∑ y ∈ J, NG.rt L n y.1 (T (ρ' (GlobalTheory.GLp.inc g n kk) (c y))) = ∑ y ∈ J, NG.rt L n y.1 (T (c y)) := by
      rw [← hx]; refine Finset.sum_congr rfl fun y _ => ?_
      rw [← hθx, ← hτθ, hTeq x hx1, rt_rt', rt_rt', (hI.2.1 x y.1 hx1 y.2).eq]
    exact hinj y (hJuniq _ _ (fun y _ => ⟨_, rfl⟩) (fun y _ => ⟨_, rfl⟩) hx' y hy)
  have hfix' : ∀ y ∈ J, ∀ kk ∈ (GlobalTheory.GLp.red g n).ker, ρ' (GlobalTheory.GLp.inc g n kk) (c y) = c y := by
    intro y hy kk hkk
    have := hfix y hy
    simp only [GlobalTheory.GLp.fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at this
    exact this ⟨kk, hkk⟩
  have hℓ' : ∀ γ, ∃ kk ∈ (GlobalTheory.GLp.red g n).ker,
      Matrix.GeneralLinearGroup.map θ.toRingHom (s.loc n (ℓ γ)) = GlobalTheory.GLp.lift g n γ * GlobalTheory.GLp.inc g n kk :=
    fun γ => GlobalTheory.T.exists_padic_lift_mul_principalCongruence_of_reduction _ s.v g n θ (fun z => (hθ z).1) _ γ (hℓ γ).2
  choose kk hkk hkkeq using hℓ'
  have hterm : ∀ γ, NG.rt L n (ℓ γ) φ = ∑ y ∈ J, NG.rt L n y.1 (T (ρ' (GlobalTheory.GLp.lift g n γ) (c y))) := by
    intro γ

    rw [hφsum, map_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [rt_rt', (hI.2.1 (ℓ γ) y.1 (hℓ γ).1 y.2).eq, ← rt_rt', ← hTeq _ (hℓ γ).1, hτθ, hkkeq, map_mul,
      Module.End.mul_apply, hfix' y hy _ (hkk γ)]
  rw [finsum_eq_sum_of_fintype]
  calc ∑ γ, a.coeff γ • NG.rt L n (ℓ γ) φ = ∑ y ∈ J, NG.rt L n y.1 (T (GlobalTheory.GLp.actK ρ' a (c y))) := by

        simp only [hterm, Finset.smul_sum, GlobalTheory.GLp.actK, LinearMap.sum_apply,
        LinearMap.smul_apply, map_sum, map_smul]
        exact Finset.sum_comm
    _ = φ := by
        rw [hφsum]
        exact Finset.sum_congr rfl fun y hy => by rw [ha _ (hfix y hy)]

theorem serFix_of_locS' {L : Type} [Field L] [NumberField L] [IsCMField L] {n g : ℕ} [Fact g.Prime]
    (π : NG.FinTyp L n) (s : SplitPlace L) {w : HeightOneSpectrum (𝓞 L)} (h : s.w = w)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion L)))
    (j : ℚ_[g] ≃+* w.adicCompletion L) (hj : Continuous j) (a : MonoidAlgebra ℂ (GL (Fin n) (ZMod g)))
    (hloc : GlobalTheory.HeightCounting.IsLocS π.S s (h ▸ τ))
    (ha : ∀ y ∈ GlobalTheory.GLp.fixK1 (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)),
      GlobalTheory.GLp.actK (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)) a y = y) :
    SerFix π s a := by
  subst h
  exact serFix_of_locS π s τ j hj a hloc ha

theorem serFix_of_comp : ∀ (D : D7) (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (cp : GlobalTheory.GoodTypes.Comp D), IsComp I rep cp → ∀ σ k v (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))), (∀ y ∈ fixK1 (cp σ k v).ρ, actK (cp σ k v).ρ a y = y) → ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → GlobalTheory.LabPin.SerFix (rep σ) s a := by
  intro D I rep cp hc σ k v a ha s hs
  obtain ⟨s₀, h₀, τ, hloc, hcp⟩ := hc σ k v
  obtain rfl : s = s₀ := GlobalTheory.T.cmSplitPlace_eq_of_prime_eq _ s s₀ (hs.trans h₀.symm)
  rw [hcp] at ha
  exact serFix_of_locS' (rep σ) s h₀ τ (I.i k v) (I.cont k v) a hloc ha

end GlobalTheory.DepthZeroSer

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DepthZeroIdentityFiniteTypeOfTypePrimeComponentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.depthZeroIdentity_finiteType_of_typePrimeComponent : ∀ (D : D7) (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (cp : GlobalTheory.GoodTypes.Comp D), IsComp I rep cp → ∀ σ k v (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))), (∀ y ∈ fixK1 (cp σ k v).ρ, actK (cp σ k v).ρ a y = y) → ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → GlobalTheory.LabPin.SerFix (rep σ) s a := by
  first | exact @GlobalTheory.DepthZeroSer.serFix_of_comp | exact GlobalTheory.DepthZeroSer.serFix_of_comp | (intros; apply GlobalTheory.DepthZeroSer.serFix_of_comp <;> assumption)
end
end
