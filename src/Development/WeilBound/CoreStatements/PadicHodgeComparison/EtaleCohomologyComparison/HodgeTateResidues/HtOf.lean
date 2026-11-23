module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EpsTA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfEtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ToYIsFirstChernIff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.CrisSurj
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.DiffMem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VnRed
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleChernClassEqKummerClass
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimResZetaX
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ForE
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Formal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.CupLeib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernClassFamily
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.Inputs
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompat
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PrepairingEtaleValue
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SmoothQ
import GroundTheory.PAdicHodge.NormalizedTraceTower
import Mathlib.RingTheory.PiTensorProduct
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Half1
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HalfGaloisOfCompatible
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.NmAMem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.PowZeroSmul
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SmulAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SumCoord
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.TfBaseField

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernCocycleAllLevels

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.HT

open CH GlobalTheory.EtC E E.Main

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem roots_eq (r r' : Roots l) : r = r' := by
  obtain ⟨ρ, h⟩ := r
  obtain ⟨ρ', h'⟩ := r'
  have : ρ = ρ' := funext fun n => Subtype.ext ((clToC l).injective ((h n).trans (h' n).symm))
  subst this
  rfl

theorem nz (n : ℕ) : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem inv_gb (r : Roots l) (M : Model l K) (n : ℕ) : GlobalTheory.EtC.Inv (l ^ n) (sch.obj (gb M)) :=
  fun U ⟨x⟩ => (Prim.map (show U ⟶ gb M from x).appTop.hom (r.zetaX M n)).2.1

theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (hn' : n' = n) (hi' : i' = i) (x : Ht q E n i) :
    (x.cast hn hi).cast hn' hi' = x := by
  subst hn hi
  rfl

theorem eM_rt (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) :
    eM lcNat H r M n i 0 (rootClass i (r.zetaX M n)) = CH.oneH (AcrEl M.P n) :=
  haveI := nz (l := l) n
  GlobalTheory.CompanionTheory.FRootCls.eM_root lcSpec morCup etRoot etIn.gen lcNat H r M n i

theorem one_cup (r : Roots l) (M : Model l K) (n : ℕ) (a : Ht (l ^ n) (sch.obj (gb M)) ((0 : ℕ) : ℤ) 0) :
    (cup (l ^ n) (show Ht (l ^ n) (sch.obj (gb M)) ((0 : ℕ) : ℤ) 0 from one (l ^ n) (sch.obj (gb M))) a).cast
      (n' := ((0 : ℕ) : ℤ)) (i' := 0) (by omega) (add_zero 0) = a :=
  haveI := nz (l := l) n
  (congrArg (Ht.cast _ _) ((formalIn.a6ring (l ^ n) (sch.obj (gb M))).1 (inv_gb r M n) a)).trans (cast_cast _ _ _ _ a)

theorem eM_one (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M))) = CH.oneH (AcrEl M.P n) := by
  have h := fCup etIn lcNat l H r K M n 0 0 0 (add_zero 0) 0 0 0 rfl (one (l ^ n) (sch.obj (gb M))) (rootClass 0 (r.zetaX M n))
  have h1 := congrArg (eM lcNat H r M n 0 0) (one_cup r M n (rootClass 0 (r.zetaX M n)))
  have h2 := congrArg ((mulP (AcrEl M.P n)).cup (add_zero 0) (eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M))))) (eM_rt H r M n 0)
  have h3 : (mulP (AcrEl M.P n)).cup (add_zero 0) (eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M)))) (CH.oneH (AcrEl M.P n)) =
      eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M))) := cupOne _ _ _ _ _
  exact h3.symm.trans (h2.symm.trans (h.symm.trans (h1.trans (eM_rt H r M n 0))))

theorem one_ex (r : Roots l) (M : Model l K) : ∃ v : M.T 0, ∀ k, v.lev k = one (l ^ k) M.spc :=
  ⟨(⟨fun k => one (l ^ k) (sch.obj (gb M)), fun k =>
      haveI := nz (l := l) (k + 1)
      ((etIn.a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l k.le_succ) _).2.1 (inv_gb r M (k + 1))).1⟩ :
    Hl l (sch.obj (gb M)) ((0 : ℕ) : ℤ) 0), fun _ => rfl⟩

theorem untw_ex (r : Roots l) (M : Model l K) (x : Hl l (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1) :
    ∃ v : Hl l (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0,
      ∀ n, v.1 n = GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) n (x.1 n) (rootClass (-1) (r.zetaX M n)) := by
  have hv : ∀ k, red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0
      (GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) (k + 1) (x.1 (k + 1)) (rootClass (-1) (r.zetaX M (k + 1)))) =
      GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) k (x.1 k) (rootClass (-1) (r.zetaX M k)) := by
    intro k
    have h1 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1 (x.1 (k + 1)) = x.1 k := x.2 k
    have h2 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((0 : ℕ) : ℤ) (-1) (rootClass (-1) (r.zetaX M (k + 1))) =
        rootClass (-1) (r.zetaX M k) := (GlobalTheory.CompanionTheory.FRootCls.rootSys etIn.op etIn.red redRoot r M (-1)).2 k
    exact (GlobalTheory.CompanionTheory.FUntwPf.vn_red etIn.a11 _ k _ _).trans (congrArg₂ (GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) k) h1 h2)
  exact ⟨⟨fun k => GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) k (x.1 k) (rootClass (-1) (r.zetaX M k)), hv⟩, fun _ => rfl⟩

theorem etale_firstChern_exists (M : Model l K) (D : LineData M.X) (r : Roots l) : ∃ v, IsEtaleFirstChernUntwisted r D v :=
  (lineBC (gb M) M.X (pullback.fst _ _ ≫ pullback.fst _ _) D).elim fun D' a => a.elim fun π hD =>
    (lineMap _ D').elim fun L hL =>
      (@chern_class_compatible_system etIn.a2 etIn.a11 l _ D'.Y (gb M) D'.f D'.sm D'.surj (isUnit_gb M) L).2.elim fun x hx =>
        (untw_ex r M x).elim fun v hv =>
          Exists.intro v (Exists.intro D' (Exists.intro π (Exists.intro L (Exists.intro (fun n => x.1 n)
            (And.intro hD (And.intro hL (And.intro hx hv)))))))

theorem firstChern_cocycle_untwisted (H : RIn l) (r : Roots l) (M : Model l K) (D : LineData M.X) (D' : LineData (gb M)) (π : D'.Y ⟶ D.Y)
    (hD : D.IsBC (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) D' π) (L : cech D'.f ⟶ ofCat (glCat 1)) (hL : D'.IsMap L)
    (n : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1) (hx : pull _ (cechAug D'.f) _ 2 x = c1 (l ^ n) L)
    (v : Ht (l ^ n) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0)
    (hv : v = GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) n x (rootClass (-1) (r.zetaX M n)))
    (C : Type 1) [Category.{0} C] (G : C ⥤ El M.P) (Λ : Lift G D) :
    ∃ (z : Cn (G ⋙ modF (AcrEl M.P n)) 2) (hz : d _ 2 z = 0), Λ.IsCoc n (tCo G n 2 z) ∧
      (cx _).cls z hz = (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (eM lcNat H r M n 0 2 v) :=
  have hI := (@chern_class_compatible_system etIn.a2 etIn.a11 l _ D'.Y (gb M) D'.f D'.sm D'.surj (isUnit_gb M) L).1 n
  have he : eM lcNat H r M n 0 2 v = eM lcNat H r M n 1 2 x :=
    (congrArg (eM lcNat H r M n 0 2) hv).trans
      (GlobalTheory.CompanionTheory.FUntwPf.step fCup cupOne etIn lcNat H r M n x _ (eM_rt H r M n (-1)))
  (E.step etale_chern_class_eq_kummer_class fKum fRes etIn lcNat H r M D D' π hD L hL n hI x hx G Λ).elim fun z c => c.2.elim fun hz e2 =>
    Exists.intro z (Exists.intro hz (And.intro c.1 (res_cls fRes etIn lcNat H r M G n x v he _ e2).symm))

theorem good_eFam (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : (eFam lcNat H r K).Good :=
  ⟨fRed etIn lcNat l H r K, fEqui etIn lcNat l H r K, fPhi lcNat l H r K, fNat etIn lcNat l H r K,
    fun M n i j x y => fCup etIn lcNat l H r K M n 0 0 0 (add_zero 0) i j (i + j) rfl x y,
    fun M => fRoot etIn lcNat l H r K M 0, firstChern_family etIn lcNat l H r K⟩

theorem firstChern_cocycle_all_levels (H : RIn l) (r : Roots l) (M : Model l K) (D : LineData M.X) (v : M.T 2) (h : IsEtaleFirstChernUntwisted r D v)
    (C : Type 1) [Category.{0} C] (G : C ⥤ El M.P) (Λ : Lift G D) (n : ℕ) :
    ∃ (z : Cn (G ⋙ modF (AcrEl M.P n)) 2) (hz : d _ 2 z = 0), Λ.IsCoc n (tCo G n 2 z) ∧
      (cx _).cls z hz = (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (eFam lcNat H r K M n 2 (v.lev n)) :=
  h.elim fun D' h => h.elim fun π h => h.elim fun L h => h.elim fun x h =>
    firstChern_cocycle_untwisted H r M D D' π h.1 L h.2.1 n (x n) (h.2.2.1 n) (v.lev n) (h.2.2.2 n) C G Λ

theorem etP_eFam (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : EtP (eFam lcNat H r K) :=
  ⟨good_eFam H r K, eM_one H r, one_ex r, etale_firstChern_exists,
    fun M D r' v h C _ G Λ n =>
      firstChern_cocycle_all_levels H r M D v (roots_eq r' r ▸ h) C G Λ n⟩

theorem etP (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : ∃ e : E.EtFam l K, EtP e :=
  (rootsEx l).elim fun r => ⟨_, etP_eFam (CrystallineSemistableComparison.R.forE l) r K⟩

end CrystallineSemistableComparison.HT
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.GTSmul

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct



namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {ht : TFil l}
  {Lf : ∀ {M : Model l K} (r : ℕ) {j : ℕ}, M.T j → Fam M r j → Prop} (h1 : Half1 ht @Lf)
  {γ : ∀ {M : Model l K} {r j : ℕ}, Fam M r j → ∀ a, Module.Dual K (Hdg M.q a j) →+ ℂ_[l]} (h2 : Half2 ht @γ)

include h1 h2 in
theorem indep {M : Model l K} (hM : M.Sm) {j r r' : ℕ} {v : M.T j} {x : Fam M r j} {x' : Fam M r' j} (hx : Lf r v x)
    (hx' : Lf r' v x') (a : ℕ) : γ x a = γ x' a := by
  obtain ⟨k, hk⟩ := h1.uniq M hM j
  have a1 := h1.sh r' (rfl : r + r' = r + r') hx
  have a2 := h1.sh r (Nat.add_comm r' r) hx'
  have e := hk (r + r') v _ _ a1 a2
  rw [← h2.sh hM r' rfl x (h1.comp hx) a, ← h2.sh hM r (Nat.add_comm r' r) x' (h1.comp hx') a,
    ← h2.sh hM k rfl _ (h1.comp a1) a, ← h2.sh hM k rfl _ (h1.comp a2) a, e]

def rr {M : Model l K} (hM : M.Sm) (j : ℕ) : ℕ := (h1.ex M hM j).choose

def xx {M : Model l K} (hM : M.Sm) {j : ℕ} (v : M.T j) : Fam M (rr h1 hM j) j := ((h1.ex M hM j).choose_spec v).choose

theorem xx_spec {M : Model l K} (hM : M.Sm) {j : ℕ} (v : M.T j) : Lf _ v (xx h1 hM v) := ((h1.ex M hM j).choose_spec v).choose_spec


variable (γ) in
def gT {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (v : M.T j) : Module.Dual K (Hdg M.q a j) →+ ℂ_[l] := γ (xx h1 hM v) a

include h2 in
theorem gT_eq {M : Model l K} (hM : M.Sm) (a : ℕ) {j r : ℕ} {v : M.T j} {x : Fam M r j} (hx : Lf r v x) :
    gT h1 (@γ) hM a v = γ x a := indep h1 h2 hM (xx_spec h1 hM v) hx a

include h2 in
theorem gT_add {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (v w : M.T j) :
    gT h1 (@γ) hM a (v + w) = gT h1 (@γ) hM a v + gT h1 (@γ) hM a w :=
  (gT_eq h1 h2 hM a (h1.add (xx_spec h1 hM v) (xx_spec h1 hM w))).trans
    (h2.add hM _ _ (h1.comp (xx_spec h1 hM v)) (h1.comp (xx_spec h1 hM w)) a)

include h2 in
theorem gT_smul {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (z : ℤ_[l]) (v : M.T j) (φ : Module.Dual K (Hdg M.q a j)) :
    gT h1 (@γ) hM a (z • v) φ = qC l (z : ℚ_[l]) * gT h1 (@γ) hM a v φ := by
  rw [gT_eq h1 h2 hM a (h1.smul z (xx_spec h1 hM v)), h2.lin hM _ _ (h1.comp (xx_spec h1 hM v)), θA_zA]
  rfl

include h2 in
theorem gT_act {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (σ : K.fixingSubgroup) (v : M.T j) (φ : Module.Dual K (Hdg M.q a j)) :
    qC l (period_ring_base.χ σ.1) ^ a * gT h1 (@γ) hM a (M.actT j σ v) φ = period_ring_base.σC σ.1 (gT h1 (@γ) hM a v φ) := by
  have e1 := gT_smul h1 h2 hM a ((DeRhamTwist.Twist.chi0 l σ.1 ^ rr h1 hM j : ℤ_[l]ˣ) : ℤ_[l]) (M.actT j σ v) φ
  replace e1 := (DFunLike.congr_fun (gT_eq h1 h2 hM a (h1.gal σ (xx_spec h1 hM v))) φ).symm.trans e1
  rw [Units.val_pow_eq_pow_val, PadicInt.coe_pow, map_pow] at e1
  have e2 := h2.gal hM σ _ (h1.comp (xx_spec h1 hM v)) a φ
  rw [e1] at e2
  have hc : qC l (period_ring_base.χ σ.1) ^ rr h1 hM j ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 (χ_ne _))
  refine mul_left_cancel₀ hc (Eq.trans ?_ e2)
  exact mul_left_comm _ _ _

def hV {M : Model l K} (hM : M.Sm) (a n : ℕ) : M.V n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]) :=
  (TensorProduct.liftAddHom (R := ℤ_[l]) (M := ℚ_[l]) (N := M.T n)
    (AddMonoidHom.mk' (fun z => AddMonoidHom.mk' (fun u =>
      AddMonoidHom.mk' (fun φ => qC l z * gT h1 (@γ) hM a u φ) (by intros; simp [mul_add]))
        (by intros; ext; simp [gT_add h1 h2, mul_add])) (by intros; ext; simp [add_mul]))
    (by
      intro r z u
      ext φ
      simp only [AddMonoidHom.mk'_apply]
      rw [gT_smul h1 h2, Algebra.smul_def, map_mul]
      simp only [PadicInt.algebraMap_apply]
      ring) :
    ℚ_[l] ⊗[ℤ_[l]] M.T n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]))


open Classical in
def hP (M : Model l K) (a n : ℕ) : M.V n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]) :=
  if hM : M.Sm then hV h1 h2 hM a n else 0

theorem hP_tmV {M : Model l K} (hM : M.Sm) (a n : ℕ) (z : ℚ_[l]) (u : M.T n) (φ : Module.Dual K (Hdg M.q a n)) :
    hP h1 h2 M a n (tmV M n z u) φ = qC l z * gT h1 (@γ) hM a u φ := by
  rw [hP, dite_eq_left hM]
  unfold hV tmV
  erw [TensorProduct.liftAddHom_tmul]
  rfl

theorem hP_toV {M : Model l K} (hM : M.Sm) (a : ℕ) {n r : ℕ} {u : M.T n} {x : Fam M r n} (hx : Lf r u x)
    (φ : Module.Dual K (Hdg M.q a n)) : hP h1 h2 M a n (M.toV n u) φ = γ x a φ := by
  rw [toV_eq, hP_tmV h1 h2 hM, map_one, one_mul, gT_eq h1 h2 hM a hx]

theorem hP_not {M : Model l K} (hM : ¬ M.Sm) (a n : ℕ) (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)) :
    hP h1 h2 M a n v φ = 0 := by
  rw [hP, dite_eq_right hM]; rfl

include h1 h2 in
theorem pre_of (hF : KFin) (hC : DlogClassExistsUnique) : Nonempty (HTPre l K) := ⟨{
  h := hP h1 h2
  lin := fun M a n z v φ => by
    by_cases hM : M.Sm
    · refine V_induction (p := fun v => hP h1 h2 M a n (z • v) φ = qC l z * hP h1 h2 M a n v φ) v ?_ ?_ ?_
      · simp only [smul_zero, map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z' u
        simp only [smul_tmV, hP_tmV h1 h2 hM, map_mul, mul_assoc]
      · intro x y hx hy
        simp only [smul_add, map_add (f := _), AddMonoidHom.add_apply, mul_add] at hx hy ⊢
        rw [hx, hy]
    · simp only [hP_not h1 h2 hM, mul_zero]
  lin' := fun M a n k v φ => by
    by_cases hM : M.Sm
    · refine V_induction (p := fun v => hP h1 h2 M a n v (k • φ) = kC K k * hP h1 h2 M a n v φ) v ?_ ?_ ?_
      · simp only [map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z' u
        simp only [hP_tmV h1 h2 hM, gT]
        rw [h2.lin' hM _ (h1.comp (xx_spec h1 hM u)), mul_left_comm]
      · intro x y hx hy
        simp only [map_add (f := _), AddMonoidHom.add_apply, mul_add] at hx hy ⊢
        rw [hx, hy]
    · simp only [hP_not h1 h2 hM, mul_zero]
  fin := fun M hM a n => by
    have := proper_q hM
    have := smooth_q hM
    exact hF M.q a n
  equi := fun M hM a n σ v φ => by
    refine V_induction (p := fun v => qC l (period_ring_base.χ σ.1) ^ a * hP h1 h2 M a n (M.act n σ v) φ =
      period_ring_base.σC σ.1 (hP h1 h2 M a n v φ)) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply, mul_zero]
    · intro z u
      simp only [act_tmV, hP_tmV h1 h2 hM]
      rw [map_mul, σC_qC, mul_left_comm, gT_act h1 h2 hM]
    · intro x y hx hy
      simp only [map_add (f := _), AddMonoidHom.add_apply, mul_add] at hx hy ⊢
      rw [hx, hy]
  nat := fun M N u hu hM hN a n v φ => by
    refine V_induction (p := fun v => hP h1 h2 M a n (Model.pullV u hu n v) φ =
      hP h1 h2 N a n v (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a n)) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply]
    · intro z w
      simp only [pullV_tmV, hP_tmV h1 h2 hM, hP_tmV h1 h2 hN]
      rw [gT_eq h1 h2 hM a (h1.nat u hu (xx_spec h1 hN w)), h2.nat u hu hM hN _ (h1.comp (xx_spec h1 hN w))]
      rfl
    · intro x y hx hy
      simp only [map_add (f := _), AddMonoidHom.add_apply] at hx hy ⊢
      rw [hx, hy]
  cup := fun M hM i j x y z hz m m' b b' c φ => by
    have hx := xx_spec h1 hM x
    have hy := xx_spec h1 hM y
    rw [hP_toV h1 h2 hM c (h1.cup rfl hz hx hy), h2.cup hM rfl _ _ (h1.comp hx) (h1.comp hy) b b' c φ]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [hP_toV h1 h2 hM _ hx, hP_toV h1 h2 hM _ hy]
  one := fun M hM v hv φ => by rw [hP_toV h1 h2 hM 0 (h1.one M v hv), h2.one hM]
  first_chern_class_exists := fun M hM D _ hD => ⟨h1.first_chern_class_exists M D, hC M.q (genD D) (sSup_pb D _ hD)⟩
  c1 := fun M hM D hE hD r v c hv hc => by
    obtain ⟨x, hx, hl⟩ := h1.c1 M D hE hD r v hv
    have := h2.c1 hM D hD x c (h1.comp hl) hx hc
    exact ⟨fun φ => (hP_toV h1 h2 hM 1 hl φ).trans (this.1 φ),
      fun a ha φ => (hP_toV h1 h2 hM a hl φ).trans (by rw [this.2 a ha]; rfl)⟩ }⟩

end CrystallineSemistableComparison.HT
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HtOf

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.HT

theorem half2 (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (hL : LvEx l K)
    (hF : KFin) : ∃ γ, Half2 (K := K) (tFil l) γ :=
  half2Of l K (tFil l) (crisSurj l) hL rhoEx (coEx l K) homRho homMu (mulRho l K) (firstChern_hodgeTate_rho l K) kForm hF

theorem ht_of (hL : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], LvEx l K)
    (hF : KFin) (hC : DlogClassExistsUnique) (hT : KTop) (hE : EtSideS) : HodgeTateMapExists := fun l _ K _ =>
  (etP l K).elim fun _ he => (half2 l K (hL l K) hF).elim fun _ h2 =>
    (pre_of (half1 (tFil l) he) h2 hF hC).elim fun P => ⟨P, inj_of P (hE l K) hT kForm he.one_ex⟩

end CrystallineSemistableComparison.HT
end
end
end
