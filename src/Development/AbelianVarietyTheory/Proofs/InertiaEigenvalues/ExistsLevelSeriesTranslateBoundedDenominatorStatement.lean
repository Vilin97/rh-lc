module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupFixVacuumTranslatesStatement
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfIntertwinesUpToScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTermsMeanZeroUnipotentRadical
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPartDenominatorBoundedByPrimePower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
public import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupHermitianLatticeEqStandard

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries



theorem GlobalTheory.LatOpen.exists_open_hLat_std : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ x ∈ J, Bridge.hLat V x = Formalism.L2.Pj.stdLat D.host.E V.rank := by
  intro D V h1
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup V 1).map (finHom V).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup V one_pos, ?_⟩
  rintro x ⟨k, hk, rfl⟩
  rw [← h1]
  have hk' := GlobalTheory.Member.PrincLevel.finCong_inv hk.2
  have hm := GlobalTheory.Member.PrincLevel.finCong_map hk.2
  have hm' := GlobalTheory.Member.PrincLevel.finCong_map hk'
  have hL := GlobalTheory.StdFrameCong.pj_latHat_eq V
  have e1 : ((((finHom V).rangeRestrict k)⁻¹ : Bridge.Gf V) :
      GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) = finHom V k⁻¹ := by
    rw [← map_inv]; rfl
  have e0 : (((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) = 1 := by
    rw [inv_one]; rfl
  unfold Bridge.hLat
  refine congrArg (Submodule.span _) (Set.ext fun v => ?_)
  show _ ∈ latHat D.host.F D.host.E (L0c D V) ↔ _ ∈ latHat D.host.F D.host.E (L0c D V)
  rw [e1, e0, Units.val_one, Matrix.one_mulVec, ← hL]
  constructor
  · intro h
    have := hm _ h
    have ekk : (finHom V k).1 * (finHom V k⁻¹).1 = 1 := by
      rw [← Units.val_mul, ← map_mul (finHom V) k k⁻¹, mul_inv_cancel k, map_one, Units.val_one]
    rwa [Matrix.mulVec_mulVec, ekk, Matrix.one_mulVec] at this
  · exact hm' _
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupHermitianLatticeEqStandardStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_open_subgroup_hermitianLattice_eq_standard : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ x ∈ J, Bridge.hLat V x = Formalism.L2.Pj.stdLat D.host.E V.rank := by
  first | exact @GlobalTheory.LatOpen.exists_open_hLat_std | exact GlobalTheory.LatOpen.exists_open_hLat_std | (intros; apply GlobalTheory.LatOpen.exists_open_hLat_std <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsThetaFunctionOfMemSpanVacuumTranslates

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem isThetaFunO_of_mem_trSp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (e : AE D) (M : ℕ) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, IsThetaFunO ψ V W f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP e M O f hf
  have hψ : IsStdChar D ψ (-1) := hP.1.weil.std
  have h0 : IsThetaFunO ψ V W f₀ := GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hP.2.2.2.2.2.2.2.2
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, -, -, rfl⟩ := hx
    exact GlobalTheory.AnisoMean.isTheta_heisO hψ h0 y
  | zero => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ V W
  | add x y _ _ hx hy => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def]
    exact GlobalTheory.LocMod.LinSpace.isThetaFunO_smul (a : ℂ) hx

end GlobalTheory.LevelSeries
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsThetaFunctionOfMemSpanVacuumTranslatesStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.isThetaFunction_of_mem_span_vacuumTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (e : AE D) (M : ℕ) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, IsThetaFunO ψ V W f := by
  first | exact @GlobalTheory.LevelSeries.isThetaFunO_of_mem_trSp | exact GlobalTheory.LevelSeries.isThetaFunO_of_mem_trSp | (intros; apply GlobalTheory.LevelSeries.isThetaFunO_of_mem_trSp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPartDenominatorBoundedByPrimePowerStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.rationalPart_denominator_bounded_by_prime_power : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ l : ℕ, l.Prime → ∀ s : GA D V, ∃ c : ℕ, ∀ z : GA D V, OneAt V l z → ∀ (γ h : GA D V) (γ' : GL (Fin V.rank) D.host.E) (k : Bridge.Gf V) (bad : ℕ), GlobalTheory.Member.IsRat V γ γ' → l ∣ bad → SplitOffBad V bad h → Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank → Bridge.hLat V k⁻¹ = Formalism.L2.Pj.stdLat D.host.E V.rank → fin V (s * z) = fin V γ * fin V h * k → DenomAt l c γ' := by
  first | exact @GlobalTheory.MoveDenom.denomAt_of_move | exact GlobalTheory.MoveDenom.denomAt_of_move | (intros; apply GlobalTheory.MoveDenom.denomAt_of_move <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelSeriesTranslateBoundedDenominator

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries



theorem exists_move_denomAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ l : ℕ, l.Prime → ∀ s ∈ GfC V, ∃ c : ℕ, ∀ z ∈ GfC V, OneAt V l z → ∀ M bad : ℕ, M ≠ 0 → bad ≠ 0 → l ∣ bad → ∃ (γ h a : GA D V) (γ' : GL (Fin V.rank) D.host.E), γ ∈ GQ V ∧ GlobalTheory.Member.IsRat V γ γ' ∧ a ∈ GinfC V ∧ γ * a ∈ GfC V ∧ SplitOffBad V bad h ∧ DenomAt l c γ' ∧ ∀ (e : AE D) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (g : GA D W), thetaKO om (s * z) g (stdF ψ θ V W sW BW f Q) = thetaKO om h g (om (a, 1) (stdF ψ θ V W sW BW f Q)) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP l hl s hs
  have hstd : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    apply SetLike.coe_injective
    rw [GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, ← hP.2.2.1, hP.2.2.2.2.2.2.1]
  obtain ⟨c, hc⟩ := GlobalTheory.T.rationalPart_denominator_bounded_by_prime_power D V hstd l hl s
  refine ⟨c, fun z hz hOne M bad hM hbad hlb => ?_⟩
  obtain ⟨J₁, hJ₁o, hJ₁⟩ := GlobalTheory.T.exists_open_subgroup_hermitianLattice_eq_standard D V hstd
  obtain ⟨J₂, hJ₂o, hJ₂⟩ := GlobalTheory.T.exists_open_subgroup_fix_vacuum_translates D ψ θ V W χV χW om ΛV ΛW sW f₀ hP M hM
  have hJo : IsOpen ((J₁ ⊓ J₂ : Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := hJ₁o.inter hJ₂o
  obtain ⟨γ, h, kJ, hsp, e⟩ := GlobalTheory.SplitRepsOpen.exists_rep_splitOffBad D V (J₁ ⊓ J₂) bad hbad hJo (fin V (s * z))
  obtain ⟨k', hk', ek⟩ := Formalism.IndefR.TopMult.exists_lift (kJ : Bridge.Gf V)
  obtain ⟨a, ha_def⟩ : ∃ a : GA D V, a = h⁻¹ * ((γ : GA D V)⁻¹ * (s * z) * k'⁻¹) := ⟨_, rfl⟩
  have hfa : finHom V a = 1 := by
    have e' := congrArg Subtype.val e
    have ek' := congrArg Subtype.val ek
    simp only [MonoidHom.coe_rangeRestrict, Bridge.ratF, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.coe_mul] at e' ek'
    rw [ha_def, map_mul, map_inv, map_mul, map_mul, map_inv, map_inv, ek', e']
    group
  have ha : a ∈ GinfC V := hfa
  have hγa : (γ : GA D V) * a ∈ GfC V := by
    have h1 : infHom V h = 1 := hsp.1
    have h2 : infHom V (s * z) = 1 := mul_mem hs hz
    have h3 : infHom V k' = 1 := hk'
    show infHom V ((γ : GA D V) * a) = 1
    rw [ha_def, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, map_inv, h1, h2, h3]
    group
  have hs' : s * z = (γ : GA D V) * (h * a) * k' := by
    rw [ha_def]; group
  obtain ⟨γ', -, hγ'⟩ := γ.2
  have hrat : GlobalTheory.Member.IsRat V (γ : GA D V) γ' := hγ'.symm
  have hkJ : (kJ : Bridge.Gf V) ∈ J₁ := (kJ.2 : (kJ : Bridge.Gf V) ∈ J₁ ⊓ J₂).1
  have hkJ' : ((kJ : Bridge.Gf V))⁻¹ ∈ J₁ := inv_mem hkJ
  have hden : DenomAt l c γ' := hc z hOne (γ : GA D V) h γ' kJ bad hrat hlb hsp (hJ₁ _ hkJ) (hJ₁ _ hkJ') e
  refine ⟨γ, h, a, γ', γ.2, hrat, ha, hγa, hsp, hden, fun e O f hf BW Q g => ?_⟩
  have hω := hP.1.weil
  have hθ : IsInfFam θ := hP.1.inf
  have hfix : om (k', 1) f = f := by
    have hk2 : fin V k' ∈ J₂ := by
      have ek2 : fin V k' = kJ := ek
      rw [ek2]; exact (kJ.2 : (kJ : Bridge.Gf V) ∈ J₁ ⊓ J₂).2
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, -, hy, rfl⟩ := hx
      exact hJ₂ k' hk' hk2 y hy
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul r x _ hx =>
      change om (k', 1) ((r : ℂ) • x) = (r : ℂ) • x
      rw [map_smul, hx]
  have hthf : IsThetaFunO ψ V W f := GlobalTheory.T.isThetaFunction_of_mem_span_vacuumTranslates D ψ θ V W χV χW om ΛV ΛW sW f₀ hP e M O f hf
  have hT : ∀ P, IsThetaFunO ψ V W (stdF ψ θ V W sW BW f P) := fun P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ hthf P
  have hk1 : om (k', 1) (stdF ψ θ V W sW BW f Q) = stdF ψ θ V W sW BW f Q := by
    have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite ψ θ V W χV χW om hθ hω (fun _ => 1) sW (fun _ => 1) BW f hT k' hk' 1
      (one_mem _) 1 (by rw [one_smul]; exact hfix) Q
    rw [one_smul] at this
    exact this
  have hp : ((s * z, g) : GA D V × GA D W) = ((γ : GA D V), 1) * ((h, g) * (a, 1)) * (k', 1) := by
    rw [hs']; simp [Prod.mk_mul_mk]
  have e1 : om (s * z, g) = om ((γ : GA D V), 1) * (om (h, g) * om (a, 1)) * om (k', 1) := by
    rw [hp, map_mul, map_mul, map_mul]
  have hth := hω.om_pres ((h, g) : GA D V × GA D W) _ (hω.om_pres ((a, 1) : GA D V × GA D W) _ (hT Q))
  show om (s * z, g) (stdF ψ θ V W sW BW f Q) 0 = om (h, g) (om (a, 1) (stdF ψ θ V W sW BW f Q)) 0
  rw [e1, Module.End.mul_apply, Module.End.mul_apply, hk1, Module.End.mul_apply,
    hω.om_aut _ γ.2 1 (one_mem _) _ hth]

end GlobalTheory.LevelSeries

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelSeriesTranslateBoundedDenominatorStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_levelSeries_translate_boundedDenominator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ l : ℕ, l.Prime → ∀ s ∈ GfC V, ∃ c : ℕ, ∀ z ∈ GfC V, OneAt V l z → ∀ M bad : ℕ, M ≠ 0 → bad ≠ 0 → l ∣ bad → ∃ (γ h a : GA D V) (γ' : GL (Fin V.rank) D.host.E), γ ∈ GQ V ∧ GlobalTheory.Member.IsRat V γ γ' ∧ a ∈ GinfC V ∧ γ * a ∈ GfC V ∧ SplitOffBad V bad h ∧ DenomAt l c γ' ∧ ∀ (e : AE D) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (g : GA D W), thetaKO om (s * z) g (stdF ψ θ V W sW BW f Q) = thetaKO om h g (om (a, 1) (stdF ψ θ V W sW BW f Q)) := by
  first | exact @GlobalTheory.LevelSeries.exists_move_denomAt | exact GlobalTheory.LevelSeries.exists_move_denomAt | (intros; apply GlobalTheory.LevelSeries.exists_move_denomAt <;> assumption)
end
end
