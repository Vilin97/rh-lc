module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecay
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EZeroThetaDescentEval

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodFix

open Formalism.L2.DIV

theorem good_fix {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (w : Fin (B.nV ℓ) → K) :
    ∑ g, (idemOf ℓ.X).coeff g • B.r g (B.S.basis.equivFun.symm (B.vE ℓ *ᵥ w)) =
      B.S.basis.equivFun.symm (B.vE ℓ *ᵥ w) := by
  set z := B.vE ℓ *ᵥ w with hz
  have hmem : z ∈ LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin := by
    have e := (image_idempotent_spec K _ (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
    rw [← e]
    exact ⟨w, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  have hid := (idempotent_central K G ℓ.X hX).1
  have hhom := group_action_matrix_hom K B.S G B.r
  have hfix : B.S.gaMat B.r (idemOf ℓ.X) *ᵥ z = z := by
    rw [← hy]
    change B.S.gaMat B.r (idemOf ℓ.X) *ᵥ (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) *ᵥ y) = B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) *ᵥ y
    rw [Matrix.mulVec_mulVec, ← hhom.2, goodAt, ← mul_assoc, hid]
  have hconv : ∀ (a : MonoidAlgebra K G) (x : Fin B.S.dim → K),
      B.S.basis.equivFun.symm (B.S.gaMat B.r a *ᵥ x) = ∑ g, a.coeff g • B.r g (B.S.basis.equivFun.symm x) := by
    intro a x
    apply B.S.basis.equivFun.injective

    rw [LinearEquiv.apply_symm_apply, map_sum]
    simp only [CSD.gaMat, Matrix.sum_mulVec, Matrix.smul_mulVec, map_smul, CSD.actMat]
    refine Finset.sum_congr rfl fun g _ => ?_
    congr 1
    have := LinearMap.toMatrix_mulVec_repr B.S.basis B.S.basis (B.r g) (B.S.basis.equivFun.symm x)
    rw [Module.Basis.equivFun_apply]
    rw [← this]
    congr 1
    funext i
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← hconv, hfix]

end GlobalTheory.GoodFix

namespace GlobalTheory.GoodFix

open Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev



theorem thDn_act (hCR : GlobalTheory.Published.CuspRapidDecay) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (h : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hC : R.IsChain) (hred : R.grp_red_R) (t : T0) (g : G)
    (x : (A.fam.R t).S.Forms) (v : (R.MY 0).Vec) :
    R.thDn t (R.jX t ((A.fam.R t).r g x)) (PiTensorProduct.tprod ℂ v) =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v)) := by
  have hS : ∀ j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j) :=
    fun j _ => @GlobalTheory.MultFinite.schurMult D R.θ _ _ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) hCR (R.νY t j) (R.fdY t j)
  refine (GlobalTheory.FormAction.act_eq_translate R hred hM.jX t g x).elim fun κ' hκ' => ?_
  refine (GlobalTheory.ChainLiftEquiv.liftsExist_chain R h t 0 (lt_of_lt_of_le two_pos D.R.two_le_m) (R.eG g)).elim fun κ hκ => ?_
  exact funext fun y =>
    (GlobalTheory.ChainLiftEquiv.thDn_shift R h hM hC t hS (R.eG g) κ' hκ'.1 (R.jX t x) (R.jX t ((A.fam.R t).r g x)) hκ'.2 κ hκ _ y).trans
      (GlobalTheory.ChainLiftEquiv.actL_zero R t (R.eG g) κ hκ _ (GlobalTheory.ChainLiftEquiv.thDn_type R t _ v) y).symm

end GlobalTheory.GoodFix

namespace GlobalTheory.GoodFix

open Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev



theorem goodProjector_fixes_compositeThetaLift_of_fixed (hCR : GlobalTheory.Published.CuspRapidDecay) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (h : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hC : R.IsChain) (hred : R.grp_red_R) (t : T0)
    (x : A.fam.amb.FR t) (hx : ∑ g, (idemOf A.X).coeff g • A.fam.amb.opR t (Sum.inr g) x = x) (v : (R.MY 0).Vec) :
    R.e0 (R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v)) = R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v) := by
  have key : R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v) = R.e0 (R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v)) := by
    conv_lhs => rw [← hx]

    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply]
    simp only [RealDat.e0, gaL, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    exact congrArg (fun z => RealDat.eC (A := A) D.what₂.embLL g • z) (thDn_act hCR R h hM hC hred t g x v)
  exact key.symm

end GlobalTheory.GoodFix
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopVectorMemExtraProjection

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLevelP

theorem toMap_shift {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0)
    (f f' : Bridge.Gf V → c.W) (hy : ∀ h, f' h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (v : Dm) (h : GA D V) :
    c.toMap pr f' v h = a⁻¹ * c.toMap pr f v (h * κ) := by
  have h1 := GlobalTheory.ThetaProjEquiv.ext_shift c hc κ hκ a ha f f' hy h
  show pr (c.ext f' h) v = a⁻¹ * pr (c.ext f (h * κ)) v
  rw [← h1, map_smul, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ ha]

theorem toMap_eigen {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0) (b : ℂ)
    (f : Bridge.Gf V → c.W) (hy : ∀ h, (b • f) h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (v : Dm) (h : GA D V) :
    a⁻¹ * c.toMap pr f v (h * κ) = b * c.toMap pr f v h :=
  (toMap_shift c hc pr κ hκ a ha f (b • f) hy v h).symm.trans
    (congrFun (LinearMap.congr_fun ((c.toMap pr).map_smul b f) v) h)

theorem mem_multT_withP {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ))
    (hu : u ∈ MultT θ M (levS V β (flag1L L)) (levChi V β (flag1L L)))
    (hP : ∀ p : P.H, ∃ κ, IsLevelLift V β L p.1 κ ∧ ∀ v h,
      (levChi V β (flagL L) κ)⁻¹ * u v (h * κ) = ((P.chi p : ℂˣ) : ℂ) * u v h) :
    u ∈ MultT θ M (levS V β (withP L P)) (levChi V β (withP L P)) := by
  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hu)
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff]
  refine ⟨hm.aut, hm.cusp, fun v k hk g => ?_, hm.equiv, hm.cont⟩
  have hT : HasType V β (flag1L L) (PiTensorProduct.lift.symm u v) := fun k hk g => hm.lev v k hk g
  refine IsPLevel.hasType (V := V) (β := β) (L := L) (P := P) ⟨hT, fun p => ?_⟩ k hk g
  obtain ⟨κ, hl, hκ⟩ := hP p
  funext h
  exact (level_action_spec hT ⟨κ, hl⟩ κ hl h).trans (hκ (PiTensorProduct.tprod ℂ v) h)

section Package

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem exists_lift_eigen (hred : R.grp_red_R) (hj : R.models_jX) (hc : R.models_cX) (t : T0) (g : G)
    (x : (A.fam.R t).S.Forms) (a : D.what₂.LL) (hx : (A.fam.R t).r g x = a • x) :
    ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ ∧ ∀ v h,
      (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ)⁻¹ * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v (h * κ) =
        D.what₂.embLL a * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v h := by
  refine (GlobalTheory.FormAction.act_eq_translate R hred hj t g x).imp fun κ hκ => ⟨hκ.1, ?_⟩
  have h3 : R.jX t ((A.fam.R t).r g x) = D.what₂.embLL a • R.jX t x :=
    (congrArg (R.jX t) hx).trans ((R.jX t).map_smulₛₗ a x)
  have h4 : (R.HX t).e (R.jX t ((A.fam.R t).r g x)) = D.what₂.embLL a • (R.HX t).e (R.jX t x) :=
    (congrArg (R.HX t).e h3).trans ((R.HX t).e.map_smul _ _)
  exact toMap_eigen R.cX hc R.prX κ hκ.1.1 _ (levChi_ne_zero (V := D.sp.X') (β := R.βX) (flagL (R.datXt t)) κ) _ _
    fun h => (congrFun h4 h).symm.trans (hκ.2 h)

theorem mem_CXP_of_good (hred : R.grp_red_R) (hj : R.models_jX) (hc : R.models_cX) (hirr : ∀ χ ∈ A.fam.X, IsAbsIrrChar χ)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T0) (x : (A.fam.R t).S.Forms)
    (hx : x ∈ Formalism.IndefR.Cx.BlockGood.goodR (A.fam.R t) (A.fam.lvl P ψ))
    (hu : R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) ∈
      MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))) :
    R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) ∈ CXP R (levPOf R.eG D.what₂.embLL P ψ) t := by
  rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq] at hx
  refine mem_multT_withP R.θ R.MX R.βX (R.datXt t) (levPOf R.eG D.what₂.embLL P ψ) _ hu fun p => ?_
  have hq : R.eG.symm p.1 ∈ P := p.2
  have ha := Formalism.IndefR.CxPass.LevelOperators.opF_goodAt_type (A.fam.R t).r A.fam.X hirr P ψ ⟨_, hq⟩ x hx
  refine (exists_lift_eigen R hred hj hc t (R.eG.symm p.1) x _ ha).imp fun κ hκ => ⟨?_, hκ.2⟩
  exact ⟨hκ.1.1, hκ.1.2.1, hκ.1.2.2.trans (R.eG.apply_symm_apply p.1)⟩

end Package

end GlobalTheory.TopLevelP

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricDatumOfFamily

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowDescent
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev geometricDatumOfFamily (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) : ((_root_.GlobalTheory.Fam.pk_z W).HX t).H :=
  (_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)
theorem apex_eq_toMap_geometricDatum (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) :
    _root_.GlobalTheory.Fam.leadingLinearMap W t F = (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F)) := rfl
theorem dn_fst_eq_dnFrom_fst {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (t : W.P.T) (hr : (f.row t).Is) :
    ∀ k, k + 1 ≤ D.R.m → ∀ (F : (f.t t).CC k) (F' : (_root_.GlobalTheory.Fam.pk_z W).CC t k), F.1 = F'.1 →
      ((f.t t).dn k F).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k F').1 := by
  intro k
  induction k with
  | zero => intro _ F F' e; exact e
  | succ k ih =>
    intro hk F F' e
    obtain ⟨h1, h2⟩ := hr.io k (by omega) F
    have e2 : (⟨F.1, h1⟩ : (_root_.GlobalTheory.Fam.pk_z W).CC t (k + 1)) = F' := Subtype.ext e
    show ((f.t t).dn k ((f.row t).io k F)).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k ((_root_.GlobalTheory.Fam.pk_z W).ioY t k F')).1
    rw [← e2]
    exact ih (by omega) _ _ h2
theorem dnFrom_fst_eq_of_heq (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) {k : ℕ} (hk : D.R.m - 1 = k) (X : (_root_.GlobalTheory.Fam.pk_z W).CC t k) (X' : (_root_.GlobalTheory.Fam.pk_z W).CC t (D.R.m - 1))
    (e : HEq X X') : (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k X).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) X').1 := by
  subst hk
  rw [eq_of_heq e]
theorem heq_eq_rec_apply (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) {M : Type} [AddCommGroup M] [Module ℂ M] {k k' : ℕ} (p : k = k')
    (g : M →ₗ[ℂ] (_root_.GlobalTheory.Fam.pk_z W).CC t k) (z : M) :
    HEq ((Eq.rec (motive := fun n _ => M →ₗ[ℂ] (_root_.GlobalTheory.Fam.pk_z W).CC t n) g p) z) (g z) := by
  subst p
  rfl

theorem down_eq_thDn {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (t : W.P.T) (hr : (f.row t).Is) (n : ℕ)
    (h : 2 * n + 2 * 0 + 2 = D.R.m) (G : (f.t t).CT) (y : ((_root_.GlobalTheory.Fam.pk_z W).HX t).H)
    (hG : G.1 = (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e y)) : _root_.GlobalTheory.MiTop.descentToLevelZero f n h t G = (_root_.GlobalTheory.Fam.pk_z W).thDn t y := by
  have H := hr.ioT (2 * n) h G
  have h' := H.choose
  have e : (((f.row t).ioT (2 * n) h G).1 : SmT ((_root_.GlobalTheory.Fam.pk_z W).MY (2 * n + 1)) →ₗ[ℂ] (GA D (Yc D (2 * n + 1)) → ℂ)) =
      (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩).1 := H.choose_spec
  have e1 := _root_.GlobalTheory.RowDescent.dn_fst_eq_dnFrom_fst f t hr (2 * n + 1) (by omega) ((f.t t).ioT (2 * n) h G) (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩) e
  have hy : (⟨G.1, h'⟩ : LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e)) =
      ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e).rangeRestrict y := Subtype.ext hG
  have e2 := _root_.GlobalTheory.RowDescent.dnFrom_fst_eq_of_heq W t (idx_top h) (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩) ((_root_.GlobalTheory.Fam.pk_z W).ioX t ⟨G.1, h'⟩)
    (_root_.GlobalTheory.RowDescent.heq_eq_rec_apply W t (idx_top h) ((_root_.GlobalTheory.Fam.pk_z W).ioX t) _)
  have e3 : (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) ((_root_.GlobalTheory.Fam.pk_z W).ioX t ⟨G.1, h'⟩)).1 = (_root_.GlobalTheory.Fam.pk_z W).thDn t y :=
    (congrArg (fun z => (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) ((_root_.GlobalTheory.Fam.pk_z W).ioX t z)).1) hy).trans
      (GlobalTheory.ChainEquiv.thDn_eq t y).symm
  have key : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = (_root_.GlobalTheory.Fam.pk_z W).thDn t y := e1.trans (e2.trans e3)
  unfold _root_.GlobalTheory.MiTop.descentToLevelZero
  exact key
theorem piTensorProduct_lift_postOn_eq_of_fixed (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (T : SmT ((_root_.GlobalTheory.Fam.pk_z W).MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ))
    (hT : ∀ v : ((_root_.GlobalTheory.Fam.pk_z W).MY 0).Vec, (_root_.GlobalTheory.Fam.pk_z W).e0 (T (PiTensorProduct.tprod ℂ v)) = T (PiTensorProduct.tprod ℂ v)) :
    PiTensorProduct.lift (postOn ((_root_.GlobalTheory.Fam.pk_z W).MY 0) (_root_.GlobalTheory.Fam.pk_z W).e0 (PiTensorProduct.lift.symm T)) = T := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, postOn_apply]
  rw [show (PiTensorProduct.lift.symm T) v = T (PiTensorProduct.tprod ℂ v) from rfl, hT v]
end GlobalTheory.RowDescent
end

theorem GlobalTheory.MiTop.linkDown_of_ok : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → _root_.GlobalTheory.MiTop.LinkDescends f := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR n h t F
  have hChar := hP.bot.hyp.2.2.2.1
  obtain ⟨⟨s, hs⟩, -⟩ := hP.lev
  have hMem : _root_.GlobalTheory.Fam.leadingLinearMap W t F ∈
      CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t :=
    GlobalTheory.TopLevelP.mem_CXP_of_good (_root_.GlobalTheory.Fam.pk_z W)
      hChar.grp.red_R hChar.models.jX hChar.models.cX hs.ok2.irr W.Q.F.P1 W.Q.F.ψ1 t
      (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F) ⟨F, rfl⟩
      ((hP.hTop t).le ⟨_, rfl⟩)
  refine ⟨⟨_root_.GlobalTheory.Fam.leadingLinearMap W t F, hMem⟩, rfl, ?_⟩
  have e1 := _root_.GlobalTheory.RowDescent.down_eq_thDn f t (hR.row t) n h ⟨_root_.GlobalTheory.Fam.leadingLinearMap W t F, hMem⟩
    (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F) (_root_.GlobalTheory.RowDescent.apex_eq_toMap_geometricDatum W t F)
  have hC : (_root_.GlobalTheory.Fam.pk_z W).IsChain := RealDat.chain_of_weak W.Q.charW.base.chain hP.ex
  have e2 : _root_.GlobalTheory.MiTop.rowFormOfTuple W t F = PiTensorProduct.lift ((_root_.GlobalTheory.Fam.pk_z W).HE.e ((_root_.GlobalTheory.Fam.pk_z W).Th t (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F))) := rfl
  have e3 := congrArg PiTensorProduct.lift (hC.Th t (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F))
  have hFixed := GlobalTheory.GoodFix.good_fix (W.P.A3.A.fam.R t)
    (W.P.A3.A.fam.lvl W.Q.F.P1 W.Q.F.ψ1) hs.ok2.irr F
  have e4 := _root_.GlobalTheory.RowDescent.piTensorProduct_lift_postOn_eq_of_fixed W _ (fun v =>
    GlobalTheory.GoodFix.goodProjector_fixes_compositeThetaLift_of_fixed
      GlobalTheory.RapidDecay.cuspRapidDecay (_root_.GlobalTheory.Fam.pk_z W)
      hChar.lev hChar.models hChar.chain hChar.grp.red_R t _ hFixed v)
  exact e1.trans (e4.symm.trans (e3.symm.trans e2.symm))
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricDatumOfFamilyStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.linkDown_of_famCh : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → _root_.GlobalTheory.MiTop.LinkDescends f := by
  first | exact @_root_.GlobalTheory.MiTop.linkDown_of_ok | exact _root_.GlobalTheory.MiTop.linkDown_of_ok | (intros; apply _root_.GlobalTheory.MiTop.linkDown_of_ok <;> assumption)
end
end
end
