module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiTContIsCrysMultV
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
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
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalKsOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IncLocChiEpsUZpow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTwistRepTwist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JTilShiftBlock
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaleRootsProdIcc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuous
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocks
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysWpRTw

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc

theorem locC_rTwO {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) = twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ := by
  let ψ : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL
  let j : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  refine MonoidHom.ext fun g => ?_
  refine Matrix.ext fun a b => ?_
  exact map_mul ψ (((chiU D.nd i 1)⁻¹ (j g) : (D.nd.O i)ˣ) : D.nd.O i) (rO D.nd i r x (j g) a b)

theorem crys_Wp_rTw : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧ ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  intro D i r ρ π w hw C _ _ hG hd
  have h2 : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    intro x
    rw [locC_rTwO]
    exact (hG w hw C).2 x
  refine ⟨?_, h2⟩
  obtain ⟨e, he⟩ := hd
  have hd' : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
    refine ⟨e, fun g u => ?_⟩
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.overK, GlobalTheory.SummandJumps.matRep_apply]
    exact he g u
  exact ((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd').1 (h2 π)).1

end GlobalTheory.UseLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiser

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLocUnif

theorem exists_uniformiser : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), ∃ lam : ↥(OL LL), Irreducible lam := by
  intro l _ LL
  obtain ⟨hdvr, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  exact IsDiscreteValuationRing.exists_irreducible ↥(OL LL)

end GlobalTheory.UseLocUnif
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtendUnramEmb

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

theorem GlobalTheory.UseLoc.extendUnramEmb : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), K.1 ≤ MaximalUnramifiedExtension l → ∀ e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1, ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e ∧ ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ'.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e → τ' = τ := by
  intro l _ K LL hK e
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) := by
    intro y
    refine ⟨⟨y.1, ⟨y.2, hK y.2⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  let φ : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
      ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩
  refine ⟨e.comp φ.symm.toAlgHom, ?_, ?_⟩
  · ext x
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    simp only [AlgHom.comp_apply]
    exact congrArg (fun z => ((e z : ↥LL.1) : Om l)) this
  · intro τ' hτ'
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    have h1 := congrArg (fun f : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 => f x) hτ'
    simp only [AlgHom.comp_apply] at h1
    rw [h1]
    simp only [AlgHom.comp_apply]
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    exact (congrArg (fun z => ((e z : ↥LL.1) : Om l)) this).symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReflSBlockJIff

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc.JumpBlock

theorem reflS_blockJ_iff (D : D7) (q : ℚ) :
    AdmissibleParameterJ.refl D q ∈ AdmissibleParameterJ.blockJ D ↔ ∃ c : ℕ, c < D.R.t ∧ q = c := by
  simp only [AdmissibleParameterJ.refl, AdmissibleParameterJ.blockJ, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc, hq⟩
    refine ⟨D.R.t - 1 - c, by omega, ?_⟩
    have h1 : 1 ≤ D.R.t := by omega
    rw [Nat.cast_sub (by omega), Nat.cast_sub h1]
    push_cast
    linarith
  · rintro ⟨c, hc, hq⟩
    refine ⟨D.R.t - 1 - c, by omega, ?_⟩
    have h1 : 1 ≤ D.R.t := by omega
    rw [Nat.cast_sub (by omega), Nat.cast_sub h1]
    push_cast
    linarith

theorem jumps_iff : ∀ (D : D7) (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) (q : ℚ),
    q ∈ AdmissibleParameterJ.JJ D up j ρ ↔ q ∈ AdmissibleParameterJ.JW D up j ρ ∨ ∃ c : ℕ, c < D.R.t ∧ q = c := by
  intro D up j ρ q
  cases up
  · simp only [AdmissibleParameterJ.JJ, AdmissibleParameterJ.JW, AdmissibleParameterJ.Jm, AdmissibleParameterJ.Jp, AdmissibleParameterJ.cloudT, AdmissibleParameterJ.lowT, AdmissibleParameterJ.reflS,
      Set.mem_union, Set.mem_setOf_eq, Bool.false_eq_true, if_false]
    rw [reflS_blockJ_iff]
  · simp only [AdmissibleParameterJ.JJ, AdmissibleParameterJ.JW, AdmissibleParameterJ.Jp, AdmissibleParameterJ.cloudT, AdmissibleParameterJ.lowT, AdmissibleParameterJ.blockJ,
      Set.mem_union, Set.mem_setOf_eq, if_true]

end GlobalTheory.UseLoc.JumpBlock
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistMRepVCont

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc
theorem twistM_repV_cont : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ), (Continuous fun g => M g) → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1)) → ∀ x, Continuous fun g => repV C (twistM (locOC C M) θ) g x := by
  intro D i w hw C k M θ hM hθ x
  have hinc : Continuous fun y : ↥(OL (D.nbr i w hw).LL) => ((incO C.le y : ↥(OL C.LL)) : ↥C.LL.1) := by
    have e : (fun y : ↥(OL (D.nbr i w hw).LL) => ((incO C.le y : ↥(OL C.LL)) : ↥C.LL.1)) =
        fun y => IntermediateField.inclusion C.le y.1 := rfl
    rw [e]
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hmat : Continuous fun g => mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g := by
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous fun g : Br.G D.nbr i w hw =>
        M ((decS D.nd w) ((Br.ι (D.nbr i w hw)) g)) a b :=
      (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.ι_cont (D.nbr i w hw)))
    have h2 := hinc.comp ((D.nbr i w hw).eO_cont.comp h1)
    have e : (fun g => mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g a b) =
        fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
          ((incO C.le ((D.nbr i w hw).eO (M ((decS D.nd w) ((Br.ι (D.nbr i w hw)) g)) a b)) : ↥(OL C.LL)) : ↥C.LL.1) := by
      funext g
      simp [mapM, twistM, locOC, Br.locO, tableLineDegreeTwo.charL, Matrix.smul_apply]
    rw [e]
    exact hθ.mul h2
  have e2 : (fun g => repV C (twistM (locOC C M) θ) g x) =
      fun g => (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g).mulVec x := by
    funext g
    rfl
  rw [e2]
  exact hmat.matrix_mulVec continuous_const
end GlobalTheory.UseLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactLocalConditionDataAtPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section
namespace GlobalTheory.UseLocInst



theorem exists_setC : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i), tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i →
    D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d →
    (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool)
      (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ),
        ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      ∃ (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)) (_ : Irreducible lam)
        (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
        (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
        (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
        (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
        SetC HW r ρ π C hA lam θ h w' η typ U := by
  intro D HW F i r ρ π hB3 hJa hGood hZ hG2 hG3 hCont hDec hEps h5 hsm hq hd hPosition w hw
  obtain ⟨C, hA⟩ := GlobalTheory.UseLoc.exists_caseA_enl D i w hw hsm hq hd
  obtain ⟨lam, hlam⟩ := GlobalTheory.UseLocUnif.exists_uniformiser (D.nd.l i) C.LL
  obtain ⟨ep, hJ⟩ := hJa
  have hτ : ∀ a : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)),
      ∃ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, tableLineDegreeTwo.Over (embC HW C hA) a τ ∧
        ∀ τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, tableLineDegreeTwo.Over (embC HW C hA) a τ' → τ' = τ :=
    fun a => GlobalTheory.UseLoc.extendUnramEmb (D.nd.l i) (D.nbr i w hw).Kw C.LL hA.1 (embC HW C hA a)
  choose τa _hτa hτu using hτ
  have hJτ := fun a => hJ i r hGood w hw C (τa a)
  choose gA ρA _hRead hX hW using hJτ
  haveI := (Br.PD D.loc D.nbr i w hw).finK₀
  haveI : NeZero (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨h, w', η, typ, U, hS, hU⟩ := hPosition _ (fun a => decide (AdmissibleParameterJ.TypeU D ep (gA a))) ρA
  obtain ⟨θ, hθc, hθcr, hθj⟩ := (hB3 (D.nd.l i) (D.nbr i w hw).Kw C.LL hA).1 (fun a => (w' a : ℤ))
  have hθj' : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ → ∀ b,
      multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b =
        if b = (w' a : ℤ) then 1 else 0 := hθj
  have hθnz : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ →
      multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ (w' a) ≠ 0 := by
    intro a τ hO
    rw [hθj' a τ hO]
    simp
  have hWp : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ → ∀ b : ℤ,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) τ b =
        ((U a).count (b + w' a) : ℤ) := by
    intro a τ hO b
    rw [hτu a τ hO, ((hW a) ρ π hZ hDec b).2.1]
    obtain ⟨h1, h2⟩ := hU a b
    by_cases hb : ((b : ℤ) : ℚ) ∈ AdmissibleParameterJ.JW D (decide (AdmissibleParameterJ.TypeU D ep (gA a))) (D.nd.j i) (ρA a)
    · rw [if_pos hb, h1.2 hb]
      simp
    · rw [if_neg hb]
      have : (U a).count (b + w' a) ≠ 1 := fun e => hb (h1.1 e)
      omega
  have hL6 := GlobalTheory.UseLoc.crys_Wp_rTw D i r ρ π w hw C hGood hZ hG2 hDec
  have hL4 := GlobalTheory.UseLoc.TwistCrysW.isCrys_and_multV D i w hw C
  have hL5 := GlobalTheory.UseLoc.twistM_repV_cont D i w hw C
  have hWcont : Continuous fun g => WpO D.nd i ρ π g :=
    (GlobalTheory.Pass.stepSub_holds D i r ρ hGood π hDec {π} rfl).1.1
  refine ⟨C, hA, lam, hlam, θ, h, w', η, typ, U, ?_, ?_⟩
  · refine ⟨D.R.t_odd.pos, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Br.PD_p]
      exact hS
    · exact hL5 _ (WpO D.nd i ρ π) θ hWcont hθc
    · exact (hL4 _ (WpO D.nd i ρ π) θ hL6.1 hθcr).1
    · intro a τ hO b
      have e := (hL4 _ (WpO D.nd i ρ π) θ hL6.1 hθcr).2 τ (w' a) (hθnz a τ hO) (b - w' a)
      rw [sub_add_cancel] at e
      rw [e, hWp a τ hO, sub_add_cancel]
    · intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
      obtain ⟨k1, k2, k3⟩ := GlobalTheory.UseLoc.chiT_cont_isCrys_multV D i r ρ π w hw C θ c hc1 hc2 hG2 hθc hθcr
      refine ⟨GlobalTheory.UseLoc.chiT_cyc D i w hw C θ c hc1 hc2, k1, k2, ?_⟩
      intro a τ hO b
      have e := k3 τ (b - ((c : ℤ) - 1))
      rw [sub_add_cancel b ((c : ℤ) - 1)] at e
      rw [e, hθj' a τ hO]
      split_ifs <;> omega
  · intro x
    refine ⟨hL5 _ (rTwO D.nd i r x) θ (GlobalTheory.Pass.FamCont.stepCont D i r hGood x).1 hθc,
      (hL4 _ (rTwO D.nd i r x) θ (hL6.2 x) hθcr).1, ?_,
      GlobalTheory.UseLoc.InstPoly.charpoly_congr D i r ρ π w hw C θ lam hlam hG3 x⟩
    intro a τ hO b
    have e := (hL4 _ (rTwO D.nd i r x) θ (hL6.2 x) hθcr).2 τ (w' a) (hθnz a τ hO) (b - w' a)
    rw [sub_add_cancel] at e
    rw [e, hτu a τ hO, ((hX a) x (b - w' a)).2.1]
    have e2 := GlobalTheory.jTil_shift_block (D.nd.l i) _ D.R.t h w' η typ U hS a
      (AdmissibleParameterJ.JW D (decide (AdmissibleParameterJ.TypeU D ep (gA a))) (D.nd.j i) (ρA a)) (hU a) (b - w' a)
    rw [sub_add_cancel] at e2
    rw [← e2]
    exact if_congr (GlobalTheory.UseLoc.JumpBlock.jumps_iff D _ _ _ _) rfl rfl

end GlobalTheory.UseLocInst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactLocalConditionDataAtPlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

theorem _root_.GlobalTheory.T.exists_exactLocalConditionData_at_place : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i), tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i →
    D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d →
    (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool)
      (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ),
        ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      ∃ (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)) (_ : Irreducible lam)
        (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
        (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
        (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
        (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
        SetC HW r ρ π C hA lam θ h w' η typ U := by
  first | exact @GlobalTheory.UseLocInst.exists_setC | exact GlobalTheory.UseLocInst.exists_setC | (intros; apply GlobalTheory.UseLocInst.exists_setC <;> assumption)
end
end
