module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SrcApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGLStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SrcApply
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.ContraUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.IsUnitaryCharInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.KeepsSB
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitaryStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairSatPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PullGoodPf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RInv2
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatTwist
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SegInv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRank
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SrcGood

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnitPf

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.compUnit :
    UpperTheory.Gal.TP.Loc.CompUnit := by
  intro E _ _ _ n U hU w hw τ hτ
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨B, hh, hp, hd, hi⟩ := GlobalTheory.DefU.Petersson.exists_invariant_pos_form E n
  obtain ⟨hirr, f, h0, hf, h2⟩ := hτ
  have key : ∀ g, ∃ x : GlobalTheory.UnitaryBC.UA E n, ∀ v, f (τ.ρ g v) = GlobalTheory.UnitaryBC.RU E n x (f v) := fun g =>
    ⟨(e.symm g).1, fun v => by
      have h3 := h2 (e.symm g) v
      have hy : ((GlobalTheory.UnitaryBC.cLoc w).comp (GlobalTheory.UnitaryBC.locU n w).subtype) (e.symm g) = g := by
        have := he (e.symm g)
        rw [e.apply_symm_apply] at this
        exact this.symm
      rw [hy] at h3
      exact h3⟩
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    have hst : ∀ g, ∀ v ∈ LinearMap.ker f, τ.ρ g v ∈ LinearMap.ker f := fun g v hv => by
      obtain ⟨x, hx⟩ := key g
      rw [LinearMap.mem_ker, hx, LinearMap.mem_ker.1 hv, map_zero]
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr).2 (LinearMap.ker f) hst with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0
  let f' : τ.V →ₗ[ℂ] GlobalTheory.DefU.autU E n := f.codRestrict _ (fun v => hU.aut _ (hf v))
  have hf' : ∀ v, f' v = 0 → v = 0 := fun v h =>
    hinj ((congrArg Subtype.val h).trans (map_zero f).symm)
  have heq : ∀ g, ∃ x, ∀ v, f' (τ.ρ g v) = GlobalTheory.DefU.autRep E n x (f' v) := fun g => by
    obtain ⟨x, hx⟩ := key g
    exact ⟨x, fun v => Subtype.ext (hx v)⟩
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v u => B (f' u) (f' v))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp), ?_, ?_, ?_⟩
  · intro v u
    simpa using (hh (f' u) (f' v)).symm
  · intro v hv
    have hne : B (f' v) (f' v) ≠ 0 := fun h => hv (hf' v (hd _ h))
    have him : (B (f' v) (f' v)).im = 0 := by
      have := congrArg Complex.im (hh (f' v) (f' v))
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    have hre : (B (f' v) (f' v)).re ≠ 0 := fun h => hne (Complex.ext h him)
    exact lt_of_le_of_ne (hp _) (Ne.symm (by simpa using hre))
  · intro g v u
    obtain ⟨x, hx⟩ := heq g
    simp only [LinearMap.mk₂'ₛₗ_apply, hx]
    exact hi x _ _
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.ContraIrr

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.contraIrr :
    UpperTheory.Gal.TP.Loc.ContraIrr := by
  intro k _ _ _ _ n V _ _ ρ hs hi
  have hadm := (GlobalTheory.Laid.bzfin_holds k).1 (Fin n) V ρ hs hi
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k n
  exact ⟨GlobalTheory.ContraRefl.contra_isIrreducible hG hadm hi, ⟨GlobalTheory.ContraRefl.evEquiv hG hadm⟩⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LeftSmooth

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.leftSmooth :
    UpperTheory.Gal.TP.Loc.LeftSmooth := by
  intro k _ _ _ _ n d Φ
  obtain ⟨hlc, hcs⟩ := Φ.2
  have key : ∀ f : GL (Fin n) k → Matrix (Fin n) (Fin d) k → Matrix (Fin n) (Fin d) k,
      Continuous (fun p : GL (Fin n) k × Matrix (Fin n) (Fin d) k => f p.1 p.2) → (∀ X, f 1 X = X) →
      ∀ᶠ g in nhds (1 : GL (Fin n) k), ∀ X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ),
        (Φ : Matrix (Fin n) (Fin d) k → ℂ) (f g X) = (Φ : Matrix (Fin n) (Fin d) k → ℂ) X := by
    intro f hf h1
    apply hcs.isCompact.eventually_forall_of_forall_eventually
    intro X₀ _
    have e1 := (hlc.comp_continuous hf).eventually_eq (1, X₀)
    have e2 := (hlc.comp_continuous
      (continuous_snd : Continuous (Prod.snd : GL (Fin n) k × Matrix (Fin n) (Fin d) k → _))).eventually_eq (1, X₀)
    filter_upwards [e1, e2] with p hp1 hp2
    simp only [Function.comp] at hp1 hp2
    rw [hp1, hp2, h1]
  have hU1 := key (fun g X => (g : Matrix (Fin n) (Fin n) k) * X)
    ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_snd) (fun X => by simp)
  have hU2 := key (fun g X => ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X)
    ((Units.continuous_coe_inv.comp continuous_fst).matrix_mul continuous_snd) (fun X => by simp)
  filter_upwards [hU1, hU2] with g hg1 hg2
  intro X
  by_cases hX : X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ)
  · exact hg1 X hX
  by_cases hgX : (g : Matrix (Fin n) (Fin n) k) * X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ)
  · have := hg2 _ hgX
    rw [← Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hgX]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LiftSatUPf

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.liftSatU :
    UpperTheory.Gal.TP.Loc.PairSat → UpperTheory.Gal.TP.Loc.CompUnit → UpperTheory.Gal.TP.Loc.LiftSatU := by
  intro hPS hCU E _ _ _ n d hnd Bs χX χW mX mW lam U U' hU hL w hw hX hW B hB
  obtain ⟨v, hvw⟩ : ∃ v, w.under (𝓞 (maximalRealSubfield E)) = v := ⟨_, rfl⟩
  have hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v := by
    obtain ⟨u, hne, hu⟩ := id hw
    subst hvw
    exact ⟨w, u, hne.symm, rfl, congrArg HeightOneSpectrum.asIdeal hu⟩
  obtain ⟨t, rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.GalOfCusp.isCMExt_real E) hv hvw
  obtain ⟨τ, hτ, hs⟩ := hB
  obtain ⟨⟨τ', hτ'⟩, -⟩ := GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E d U' hL.aut _ hw
  exact ⟨τ', hτ', hPS E n d hnd v t χX χW τ τ' (hL.loc v t τ τ' hτ hτ')
    (hCU E n U hU _ hw τ hτ) hX hW B hs⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.ModelDict

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.modelDict :
    UpperTheory.Gal.TP.Loc.ModelDict := by
  intro k _ _ _ _ n d ν b g h Ψ X
  have hM : ((((GlobalTheory.SplitFlip.invT g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
      ((GlobalTheory.SplitFlip.invT h : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)).transpose =
      ((h⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) * X.transpose * (g : Matrix (Fin n) (Fin n) k) := by
    rw [GlobalTheory.SplitFlip.invT_inv_val, GlobalTheory.SplitFlip.invT_val, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hg := nabs_pos k (Matrix.GeneralLinearGroup.det g)
  have hh := nabs_pos k (Matrix.GeneralLinearGroup.det h)
  unfold GlobalTheory.SplitFlip.omA om
  rw [GlobalTheory.SplitFlip.gdet_invT, GlobalTheory.SplitFlip.apow_inv]
  beta_reduce
  rw [hM]
  simp only [GlobalTheory.SplitFlip.apow, GlobalTheory.SplitFlip.gdet, Fintype.card_fin]
  rw [Complex.ofReal_cpow hg.le, Complex.ofReal_cpow hh.le]
  simp only [map_inv, inv_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    neg_div, neg_neg, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  have hb : ((b (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatContra

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.satContra :
    UpperTheory.Gal.TP.Loc.ContraUnit → UpperTheory.Gal.TP.Loc.SatContra := by
  intro hCU K _ _ w n V _ _ ρ hs hi hu B hB
  obtain ⟨-, C, hC⟩ := hCU (w.adicCompletion K) n V ρ hs hi hu
  obtain ⟨b, -, hp, hinv⟩ := hu
  refine UpperTheory.V.Af.Gk.satConj K n w V (smoothPart ρ.dual) ρ (contra ρ) b.flip C ?_ ?_ hC B hB
  · intro x hx
    by_contra h0
    have h1 := hp x h0
    have h2 : b x x = 0 := hx
    rw [h2] at h1
    simp at h1
  · intro g x y
    exact hinv g y x
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatInvT

section

@[expose] public section

noncomputable section

namespace UpperTheory.Gal.TP.Loc

theorem satInvT : SatInvT := by
  intro K _ _ w n V _ _ ρ B h
  refine UpperTheory.V.InvT.hasSatGL_invT (ρ := ρ) (LinearEquiv.refl ℂ V) (fun g x => ?_) h
  have hg : GlobalTheory.SplitFlip.invT g = GlobalTheory.CuspRep.invT n _ g := Units.ext rfl
  change ρ (GlobalTheory.SplitFlip.invT g) x = ρ (GlobalTheory.CuspRep.invT n _ g) x
  rw [hg]

end UpperTheory.Gal.TP.Loc

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.Separates

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.separates :
    UpperTheory.Gal.TP.Loc.Separates := by
  intro k _ _ _ _ n V _ _ ρ hρ v hv
  exact GlobalTheory.ContraRefl.exists_smooth_form_ne hρ (GlobalTheory.ThetaLiftGL.compactOpen_basis k n) hv
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LiftSatUHolds

section

@[expose] public section

namespace UpperTheory.Gal.TP.Loc

theorem liftIso_holds : LiftIso :=
  liftIso_of (pairOfLift leftSmooth keepsSB modelDict separates) srcGood contraIrr (contraUnit contraIrr)

theorem liftSat_holds : LiftSat :=
  liftSat_of liftIso_holds srcGood contraIrr (contraUnit contraIrr) (satContra (contraUnit contraIrr)) satTwist satInvT satDet
    satProd segInv

theorem pairSat_holds : PairSat :=
  pairSat liftSat_holds pullGood contraIrr (contraUnit contraIrr) (satContra (contraUnit contraIrr))

theorem liftSatU_holds : LiftSatU := liftSatU pairSat_holds compUnit

end UpperTheory.Gal.TP.Loc
end
end
