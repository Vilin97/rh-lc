module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocComm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MatEqOfComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAtApart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongGrpEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFacEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNFact
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLatCoord
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLocComm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.WhittakerSupportTildeOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option linter.unusedSectionVars false

namespace WhittakerInverseTranspose

section Tilde

theorem invT_invT' {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R g) = g := Units.ext rfl

theorem val_invT' {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    ((GlobalTheory.CuspRep.invT n R g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ := rfl

theorem continuous_invT' (N : ℕ) : Continuous (GlobalTheory.CuspRep.invT N k) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSmooth_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : IsSmooth ρ) :
    IsSmooth (ρ.comp (GlobalTheory.CuspRep.invT N k)) :=
  fun v => (h v).preimage (continuous_invT' N)

theorem isIrreducible_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp (GlobalTheory.CuspRep.invT N k)) := by
  let Φ : Subrepresentation (ρ.comp (GlobalTheory.CuspRep.invT N k)) ≃o Subrepresentation ρ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        rw [← invT_invT' N g]
        exact U.apply_mem_toSubmodule (GlobalTheory.CuspRep.invT N k g) hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule _ hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have : IsSimpleOrder (Subrepresentation ρ) := h
  exact Φ.isSimpleOrder

theorem mem_unipRad_iff' {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) (g : GL (Fin N) k) :
    g ∈ unipRad k e ↔ ∀ x y, ((e.symm y).1 < (e.symm x).1 → (g : Matrix (Fin N) (Fin N) k) x y = 0) ∧
      ((e.symm x).1 = (e.symm y).1 →
        (g : Matrix (Fin N) (Fin N) k) x y = (1 : Matrix (Fin N) (Fin N) k) x y) := by
  rw [mem_unipRad, mem_parab_iff]
  constructor
  · rintro ⟨h1, h2⟩ x y
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
    simp only [Equiv.symm_apply_apply]
    refine ⟨fun hab => h1 a b i j hab, fun hab => ?_⟩
    subst hab
    rw [h2 a i j]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne]
      intro h; exact hij (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective h)).2)
  · intro h
    refine ⟨fun a b i j hab => (h _ _).1 (by simpa using hab), fun a i j => ?_⟩
    rw [(h _ _).2 (by simp)]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne]
      intro h'; exact hij (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective h')).2)

theorem invT_mem_unipRad {s N : ℕ} {d d' : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    (e' : (Σ a, Fin (d' a)) ≃ Fin N) (he : ∀ x, (e'.symm x).1 = Fin.rev (e.symm x).1) {g : GL (Fin N) k}
    (hg : g ∈ unipRad k e) : GlobalTheory.CuspRep.invT N k g ∈ unipRad k e' := by
  have hi := (mem_unipRad_iff' e _).1 (inv_mem hg)
  refine (mem_unipRad_iff' e' _).2 fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩
  · rw [val_invT', Matrix.transpose_apply]
    refine (hi y x).1 ?_
    rw [he, he] at hxy
    exact Fin.rev_lt_rev.1 hxy
  · rw [val_invT', Matrix.transpose_apply, (hi y x).2 ?_]
    · by_cases hxy' : x = y
      · subst hxy'; rfl
      · rw [Matrix.one_apply_ne hxy', Matrix.one_apply_ne (Ne.symm hxy')]
    · rw [he, he] at hxy; exact (Fin.rev_injective hxy).symm

theorem isCuspidal_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : IsCuspidal ρ) :
    IsCuspidal (ρ.comp (GlobalTheory.CuspRep.invT N k)) := by
  refine ⟨isSmooth_comp_invT h.1, fun s d e hne => ?_⟩
  let e' : (Σ a, Fin (d (Fin.revPerm a))) ≃ Fin N :=
    (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).trans e
  have he : ∀ x, (e'.symm x).1 = Fin.rev (e.symm x).1 := fun x => by
    have h1 : e'.symm x = (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).symm (e.symm x) := rfl
    obtain ⟨⟨a, i⟩, hq⟩ : ∃ q, (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).symm (e.symm x) = q :=
      ⟨_, rfl⟩
    have h2 := congrArg (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm) hq
    rw [Equiv.apply_symm_apply, Equiv.sigmaCongrLeft_apply] at h2
    rw [h1, hq, h2]
    simp
  have he' : ∀ x, (e.symm x).1 = Fin.rev (e'.symm x).1 := fun x => by rw [he, Fin.rev_rev]
  have hne' : unipRad k e' ≠ ⊥ := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨_, invT_mem_unipRad e e' he hg⟩, fun h1 => hg1 ?_⟩
    have h2 : GlobalTheory.CuspRep.invT N k g = 1 := congrArg Subtype.val h1
    refine Subtype.ext ?_
    show g = 1
    rw [← invT_invT' N g, h2, map_one]
  have hs := h.2 s (fun a => d (Fin.revPerm a)) e' hne'
  have htop : twKer ρ (unipRad k e') 1 = ⊤ := Submodule.Quotient.subsingleton_iff.1 hs
  show Subsingleton (V ⧸ twKer _ _ 1)
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff, ← htop]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  refine Submodule.subset_span ⟨⟨GlobalTheory.CuspRep.invT N k n, invT_mem_unipRad e' e he' n.2⟩, v, ?_⟩
  simp [invT_invT']

end Tilde

end WhittakerInverseTranspose

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCuspTh

section

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pCuspTh :
    CuspTh := by
  intro E _ _ _ n w σ
  let σ' : SmIrr (GLw n w) :=
    { V := σ.V
      ρ := σ.ρ.comp (invT n (w.adicCompletion E))
      smooth := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isSmooth_comp_invT σ.smooth
      irred := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isIrreducible_comp_invT σ.irred }
  refine ⟨σ', LinearEquiv.refl ℂ _, fun g g' v h => ?_, fun hc => ?_⟩
  · have hg : g' = invT n (w.adicCompletion E) g := Units.ext h
    subst hg
    show σ.ρ (invT n _ (invT n _ g)) v = σ.ρ g v
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT']
  · have h2 := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isCuspidal_comp_invT (ρ := σ'.ρ) hc
    have h3 : σ'.ρ.comp (invT n (w.adicCompletion E)) = σ.ρ :=
      MonoidHom.ext fun g => by
        show σ.ρ (invT n _ (invT n _ g)) = σ.ρ g
        rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT']
    rwa [h3] at h2
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ContinuousInvT

section

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw invT_val invT_invT')
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc

private theorem continuous_invT' {n : ℕ} {R : Type} [CommRing R] [TopologicalSpace R] :
    Continuous (invT n R : GL (Fin n) R → GL (Fin n) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_coe_inv.matrix_transpose
  · have e : (fun g : GL (Fin n) R => ((invT n R g)⁻¹ : GL (Fin n) R).val) = fun g => g.valᵀ := by
      funext g
      rw [← map_inv, invT_val, inv_inv]
    rw [e]
    exact Units.continuous_val.matrix_transpose

private theorem tyTop_of (hF : KNFact) (hG : CongGrpEx) (hC : CuspTh) : TyTop := by
  intro E _ _ _ A n p _ S F x U w₀ Up V _ _ _ _ hq r W _ N _ _ L hw Ty hT
  obtain ⟨q, hq, hgood, hqw⟩ := hq
  have hN : 0 < N.1 := lt_of_lt_of_le (by norm_num) N.2.1
  have hJ : ∀ y : GLw n w₀, y ∈ Ty.J ↔ invT n _ y ∈ V.J := fun y => hT.J_iff y _ (invT_val y)
  have hJo : IsOpen (V.J : Set (GLw n w₀)) := V.Kw0 ▸ V.shape.opn w₀ V.shape.mem
  have hJc : IsCompact (V.J : Set (GLw n w₀)) := V.Kw0 ▸ V.shape.cpt w₀ V.shape.mem
  refine ⟨GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p _ _ S.L N.1 hN, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨K, hK, ho, hc, -⟩ := hG E n N.1 hN w₀
    refine ⟨K, ho, hc, ?_⟩
    rw [hT.L_eq, hT.K₀_eq]
    exact hF E A n p S F ⟨w₀, hw⟩ _ (hT.fac _) q hq hgood hqw N.1 hN K hK
  · have e : (Ty.J : Set (GLw n w₀)) = invT n _ ⁻¹' (V.J : Set (GLw n w₀)) := Set.ext hJ
    rw [e]
    exact hJo.preimage continuous_invT'
  · have e : (Ty.J : Set (GLw n w₀)) = invT n _ '' (V.J : Set (GLw n w₀)) := by
      ext y
      constructor
      · intro hy
        exact ⟨_, (hJ y).1 hy, invT_invT' y⟩
      · rintro ⟨y', hy', rfl⟩
        exact (hJ _).2 (by rwa [invT_invT'])
    rw [e]
    exact hJc.image continuous_invT'
  · have hc : Continuous (fun y : Ty.J => (⟨invT n _ y.1, (hJ y.1).1 y.2⟩ : V.J)) :=
      (continuous_invT'.comp continuous_subtype_val).subtype_mk _
    have e : (Ty.ψ.ker : Set Ty.J) =
        (fun y : Ty.J => (⟨invT n _ y.1, (hJ y.1).1 y.2⟩ : V.J)) ⁻¹' {k : V.J | V.χ k = 1} := by
      ext y
      have h := hT.ψ_eq y ⟨invT n _ y.1, (hJ y.1).1 y.2⟩ (invT_val y.1)
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_ofPred_eq, h]
    rw [e]
    exact V.ker_open.preimage hc
  · intro σ v hv hσ
    obtain ⟨σ', e, he, hcusp⟩ := hC E n w₀ σ
    refine hcusp (V.cusp σ' (e v) (fun h => hv (e.map_eq_zero_iff.1 h)) fun g => ?_)
    have hg : invT n _ g.1 ∈ Ty.J := (hJ _).2 (by rw [invT_invT']; exact g.2)
    have hval : (g : GLw n w₀).val = ((invT n _ g.1)⁻¹).valᵀ := by
      rw [← invT_val, invT_invT']
    rw [he _ _ v hval, hσ ⟨_, hg⟩, map_smul, hT.ψ_eq ⟨_, hg⟩ g hval]

theorem UpperTheory.Gal.Spc.tyTop :
    UpperTheory.Gal.Spc.TyTop :=
  tyTop_of (pKNFact (pKNIff (pLatCoord pRepLaws)) pFacEq (pAtApart pJEq) pCongGrpEx (pCongConj UpperTheory.Gal.CertificateRingHomMap.pLocComm_of) pLocComm
    UpperTheory.Gal.CertificateRingHomMap.pLocComm_of) pCongGrpEx pCuspTh
end
end
