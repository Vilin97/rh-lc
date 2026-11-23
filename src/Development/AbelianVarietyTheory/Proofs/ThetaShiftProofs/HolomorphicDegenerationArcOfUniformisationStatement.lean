module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionOverZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelPointTangentVectorTransportIffStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LevelPointsOfArcEqPeriodDivLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmpCongrOfExEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfRationalPoints
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CoeffFSumDerivEqFderiv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLatticeVectorRepAndShift
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRingHomLift
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermsSpecStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsHolToCompClm
public import Mathlib.RingTheory.LaurentSeries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyChainArcWitnessUniversalFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointsFramesEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SpecPtsIsFibAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SpecPtsNonempty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CardQkOfTateIsoQ

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.ArcPts
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem card_qk_pre (hL : Out.Laws) (hL2 : Out.Laws2) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (D₀ : Out.DegPre R) (hB : D₀.TauBimult) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    (k : ℕ) (hk : (k : F) ≠ 0) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ (2 * (D₀.rank + D₀.P.g)) := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  have h₁ := (GlobalTheory.GtCount.card_gtTors hL hL2 R D₀ F k hk).1
  simp only [GlobalTheory.GtCount.gtTors_iff] at h₁
  open ReciprocityTheory.ChartRestriction.G.Out in
  have hc : Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) =
      k ^ D₀.rank * Nat.card {g : GtPtF D₀ F // k • g = 0} := by
    open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR in
      let iota : D₀.X →+ GtPtF D₀ F := AddMonoidHom.mk' (fun x => (exists_iota (F := F) hB x).choose) fun x x' => by
        obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x).choose_spec
        obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x').choose_spec
        obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB (x + x')).choose_spec
        refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
        have C : IsCub (th D₀ (T := TF (R := R) F) y J) := isCub_cubV D₀.cub hJ
        rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
        exact tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
      have hi (x : D₀.X) : GtPtF.IsIota x (iota x) := (exists_iota (F := F) hB x).choose_spec
      have he (x : D₀.X) (g : GtPtF D₀ F) : GtPtF.IsIota x g ↔ g = iota x :=
        ⟨fun h => isIota_unique h (hi x), fun h => h ▸ hi x⟩
      let qkMk (y : D₀.X) (g : GtPtF D₀ F) (h : k • g = iota y) : QkPt D₀ F k :=
        ⟨y, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, (he _ _).2 h⟩
      have qk_nsmul (p : QkPt D₀ F k) : k • p.g = iota p.y := by
        obtain ⟨h, h₁, h₂⟩ := p.eq
        exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((he _ _).1 h₂)
      have equiv_iff (p p' : QkPt D₀ F k) : QkPt.Equiv D₀ F p p' ↔ ∃ z : D₀.X, p'.y = p.y + k • z ∧ p'.g = p.g + iota z :=
        exists_congr fun z => and_congr Iff.rfl
          ⟨fun ⟨_, h₁, h₂⟩ => ((isAdd_iff_eq _ _ _).1 h₂).trans (congrArg (p.g + ·) ((he _ _).1 h₁)),
           fun h => ⟨_, hi z, (isAdd_iff_eq _ _ _).2 h⟩⟩
      have hd : ∀ y : D₀.X, ∃ g : GtPtF D₀ F, k • g = iota y :=
        fun y => exists_nsmul_eq hL.mulN (Or.inl inferInstance) hk0 _
      choose r hr using hd
      let K : AddSubgroup D₀.X := (nsmulAddMonoidHom k : D₀.X →+ D₀.X).range
      have hK : Nat.card (D₀.X ⧸ K) = k ^ D₀.rank := AddSubgroup.index_range_nsmul D₀.X k
      let f : (D₀.X ⧸ K) × {g : GtPtF D₀ F // k • g = 0} → Quot (Out.QkPt.Equiv D₀ F (k := k)) := fun x =>
        Quot.mk _ (qkMk x.1.out (r x.1.out + x.2.1) (by rw [nsmul_add, hr, x.2.2, add_zero]))
      rw [← hK, ← Nat.card_prod]
      refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
      · rintro ⟨c, t⟩ ⟨c', t'⟩ h
        obtain ⟨z, hy, hg⟩ := (equiv_iff _ _).1 ((equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact h))
        change c'.out = c.out + k • z at hy
        change r c'.out + t'.1 = r c.out + t.1 + iota z at hg
        obtain rfl : c = c' := by
          rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq]
          exact ⟨z, by rw [hy, neg_add_cancel_left]; rfl⟩
        have hz : z = 0 := by
          have h0 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact left_eq_add.1 hy
          exact (smul_eq_zero.1 h0).resolve_left (by exact_mod_cast hk0)
        rw [hz, map_zero, add_zero, add_right_inj] at hg
        exact Prod.ext rfl (Subtype.ext hg.symm)
      · rintro ⟨p⟩
        obtain ⟨z, hz⟩ : -p.y + (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out ∈ K := by
          rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
        have hy : (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out = p.y + k • z := by
          rw [show k • z = _ from hz, add_neg_cancel_left]
        refine ⟨⟨QuotientAddGroup.mk p.y, p.g + iota z - r (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out, ?_⟩,
          (Quot.sound ((equiv_iff _ _).2 ⟨z, hy, ?_⟩)).symm⟩
        · rw [nsmul_sub, hr, hy, nsmul_add, qk_nsmul, map_add (f := _), map_nsmul, sub_self]
        · exact add_sub_cancel _ _
  rw [hc, h₁, ← pow_add]
  congr 1
  ring

theorem card_qk_of_tateIsoQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {R : Type} [CommRing R] [IsDomain R] {D₀ : Out.DegPre R} [Module (𝓞 E) D₀.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (hB : D₀.TauBimult) (I : TateIsoQ D D₀ oa F) (k : ℕ) (hk : 0 < k) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ Module.finrank ℤ D.La := by
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have := datum_free_int D
  let K : AddSubgroup D.La := (nsmulAddMonoidHom k : D.La →+ D.La).range
  have hK : Nat.card (D.La ⧸ K) = k ^ Module.finrank ℤ D.La := AddSubgroup.index_range_nsmul D.La k
  have hE := equiv_equivalence (D := D₀) (F := F) (k := k) hB
  let f : D.La ⧸ K → Quot (Out.QkPt.Equiv D₀ F (k := k)) := fun x => Quot.mk _ (I.ev k x.out)
  rw [← hK]
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · intro x x' h
    obtain ⟨e, he⟩ := (I.ker k hk _ _).1 (hE.symm (hE.eqvGen_iff.1 (Quot.eqvGen_exact h)))
    rw [← QuotientAddGroup.out_eq' x, ← QuotientAddGroup.out_eq' x', QuotientAddGroup.eq]
    exact ⟨e, by rw [he, neg_add_cancel_left]; rfl⟩
  · rintro ⟨p⟩
    obtain ⟨v, hv⟩ := I.onto k hk p
    obtain ⟨e, he⟩ : -v + (QuotientAddGroup.mk v : D.La ⧸ K).out ∈ K := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    refine ⟨QuotientAddGroup.mk v, Quot.sound (hE.trans ((I.ker k hk _ _).2 ⟨e, ?_⟩) hv)⟩
    rw [show k • e = _ from he, add_neg_cancel_left]

theorem finrank_V_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → (∃ r z : O, ((β r : c.F) : ℂ) = H.rt0 ∧ ((β z : c.F) : ℂ) = zeta l.A) → Module.finrank ℂ Λ.A.V = g := by
  intro hL hL2 E _ _ _ H _ D l c O _ β _ _ b a Λ g ty hty ⟨r, z, hr, hz⟩
  obtain ⟨-, I, -⟩ := a.geom ℂ r z hr hz _ rfl
  have h₁ := card_qk_pre hL hL2 a.D₀ a.bimult ℂ 2 (by norm_num)
  rw [card_qk_of_tateIsoQ a.bimult I 2 two_pos, datum_finrank_int,
    ← (GlobalTheory.PeriodExists.period_of_isTypeFn H D g ty hty).1] at h₁
  have h₂ := Nat.pow_right_injective le_rfl h₁
  have h₃ : Module.finrank ℤ Λ.A.X = a.D₀.rank := (Λ.ε.toAddEquiv.toIntLinearEquiv).finrank_eq
  rw [Λ.A.finrank_V, h₃, Λ.gB_eq]
  omega

end GlobalTheory.ArcPts
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ChainLevelPtOfSection

section

@[expose] public section

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem chain_levelPt_of_section (h1 : Out.Laws) (h2 : Out.Laws2) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ)
    (k : ℕ) [NeZero k] (p₀ : Out.QkPt a.D₀ (FractionRing ℂ) k) (ξ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G)
    (ξ₀ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (la : Λ.A.La)
    (hξ : ξ.left ≫ Y.m0.toSABMap.φ = pullback.fst _ _ ≫ ξ₀.left)
    (hk : (k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ ξ = Y.oF.etaA v) ∨
      (k = l.M ∧ ∃ v ∈ idealPart D l, HEq p₀ (a.eta v) ∧ ξ = Y.oF.eta v))
    (hrep : Λ.Rep k p₀ la) : C.Φ.LevelPt k (toUnit _ ≫ ξ₀) la := by
  have hξw : ξ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w ξ
  have hY : (C.yF ≫ ξ.left ≫ Y.m.φ) ≫ Y.t.G.hom = gen ≫ χ := by
    have := Y.m.cart.1.w
    rw [Category.assoc, Category.assoc, this, ← Category.assoc ξ.left, hξw, Category.id_comp]
    exact C.yF_j
  let p : Over.mk gen ⟶ W.t.G :=
    Over.homMk (W.m.cart.1.lift (C.yF ≫ ξ.left ≫ Y.m.φ) gen hY) (W.m.cart.1.lift_snd _ _ _)
  have hp : p.left ≫ W.m.φ = C.yF ≫ ξ.left ≫ Y.m.φ := W.m.cart.1.lift_fst _ _ _
  let pY : Over.mk (gen ≫ χ) ⟶ Y.t.G := Over.homMk (C.yF ≫ ξ.left ≫ Y.m.φ) hY
  let pF : Over.mk C.yF ⟶ Y.oF.t.G := toUnit _ ≫ ξ
  have hpF : pF.left = C.yF ≫ ξ.left := rfl
  have hW := GlobalTheory.T.levelPoints_of_arc_eq_period_div_level h1 h2 E H D l Xo c O β Y (bF.comp β) a χ W Λ C.Ξ C.ΦW C.yF k p₀ ξ la p C.isGen C.yF_j
    hk hrep hp
  have h₂ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ W.m C.w₂ _ _ C.ΦW C.ΦY C.rig₂.1 C.rel₂).1 k p pY la hp
  have h₁ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ Y.m C.w₁ _ _ C.ΦF C.ΦY C.rig₁.1 C.rel₁).1 k pF pY la
    (by rw [hpF, Category.assoc]; rfl)
  have h₀ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ Y.m0.toSABMap C.w₀ _ _ C.ΦF C.Φ C.rig₀.1 C.rel₀).1 k pF
    (toUnit _ ≫ ξ₀) la (by rw [hpF, Category.assoc, hξ, ← Category.assoc]; rfl)
  exact h₀.1 (h₁.2 (h₂.1 hW))

theorem chain_levels : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (laA laM : D.La → Λ.A.La), (∀ v, Λ.Rep l.A (a.etaA v) (laA v)) → (∀ v, Λ.Rep l.M (a.eta v) (laM v)) → (∀ v, C.Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v)) ∧ ∀ v ∈ idealPart D l, C.Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v) := by
  intro h1 h2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C laA laM hA hM
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · exact chain_levelPt_of_section h1 h2 E H D l Xo c O β Y bF a χ W Λ C l.A (a.etaA v) (Y.oF.etaA v)
      (Xo.univ.etaA v) (laA v) (Y.m0.etaA v) (Or.inl ⟨rfl, v, HEq.rfl, rfl⟩) (hA v)
  · exact chain_levelPt_of_section h1 h2 E H D l Xo c O β Y bF a χ W Λ C l.M (a.eta v) (Y.oF.eta v)
      (Xo.univ.eta v) (laM v) (Y.m0.eta v) (Or.inr ⟨rfl, v, hv, HEq.rfl, rfl⟩) (hM v)

end GlobalTheory.ArcPts
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFactor

section

@[expose] public section

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem exists_isFactor : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∃ (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ), IsFactor A lin cst ∧ ∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la' := by
  intro O _ _ A
  refine ⟨fun _ la => A.lin la, A.logConst, fun w la v j α th h m => ?_, fun w la la' => ?_⟩
  · rw [A.term_add_period h w la m v, A.perFactor_eq_exp, A.L_apply]
  · rw [A.lin_Pw_sub]; ring

end GlobalTheory.ArcPts
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsHolToHalfPlaneMono

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

namespace GlobalTheory.HolomorphicArc

theorem map_nsmul_eq_pow {L G : Type} [AddCommGroup L] [Group G] (f : L → G) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : L) : f (n • a) = f a ^ n := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.1 h.symm
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem nsmul_mem (v : D.La) : l.M • v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  have h' : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left h
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul h' Submodule.mem_top

theorem over_of_generic {S : Scheme.{0}} {k : Type} [CommRing k] (s : S ⟶ Sp k) (σ : k →+* ℂ)
    (R : Subalgebra ℂ ℂ⸨X⸩) (y : Sp R ⟶ S) (ev : R →ₐ[ℂ] ℂ)
    (h : (spMap R.val.toRingHom ≫ y) ≫ s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ)) :
    (spMap ev.toRingHom ≫ y) ≫ s = spMap σ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (y ≫ s)
  have h₁ : y ≫ s = spMap φ.hom := hφ.symm
  rw [Category.assoc, h₁, ← spMap_comp] at h ⊢
  have h₂ := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  congr 1
  ext x
  have h₃ : φ.hom x = algebraMap ℂ R (σ x) := Subtype.ext (DFunLike.congr_fun h₂ x)
  exact (congrArg ev h₃).trans (ev.commutes _)

theorem isHolTo_halfPlane_mono {X : Scheme.{0}} {y : ℂ → (Sp ℂ ⟶ X)} {T T' : ℝ} (h : T ≤ T')
    (hol : IsHolTo {w : ℂ | T < w.im} y) : IsHolTo {w : ℂ | T' < w.im} y := by
  intro U f
  have e : {b | b ∈ {w : ℂ | T' < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U} =
      {w : ℂ | T' < w.im} ∩ {b | b ∈ {w : ℂ | T < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun b => ⟨fun hb => ⟨hb.1, h.trans_lt hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
  rw [e]
  exact ⟨(isOpen_lt continuous_const Complex.continuous_im).inter (hol U f).1,
    (hol U f).2.mono Set.inter_subset_right⟩

end GlobalTheory.HolomorphicArc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicDegenerationArcOfUniformisation

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.HolomorphicArc

theorem main : ReciprocityTheory.ChartRestriction.G.Out.Laws → ReciprocityTheory.ChartRestriction.G.Out.Laws2 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition := by
  intro L₁ L₂ hU E _ _ _ H D l Xo c O _ β Y bF _ _ a χ W g ty Fu _ hty hrz hχ hgen
  letI := H.starRing
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  haveI : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨Λ⟩ := GlobalTheory.ArcModel.nonempty_gtAn L₁ L₂ hU E H D l c O β _ a
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_chain_arc_witness_universal_family L₁ L₂ E H D l Xo c O β Y bF a χ W Λ hχ hgen
  choose laA hA using fun v => (GlobalTheory.GtRep.exists_rep_and_shift L₁ L₂ E H D l c O β _ a Λ l.A l.A_pos).1 (a.etaA v)
  choose laM hM using fun v => (GlobalTheory.GtRep.exists_rep_and_shift L₁ L₂ E H D l c O β _ a Λ l.M (le_trans (by norm_num) l.three_le)).1 (a.eta v)
  obtain ⟨levA, levM⟩ := GlobalTheory.ArcPts.chain_levels L₁ L₂ E H D l Xo c O β Y bF a χ W Λ C laA laM hA hM
  have hfin : AnFin Λ.A := (GlobalTheory.ArcThetaSpaces.sections_theta L₁ L₂ E H D l c O β _ a Λ).2.1
  have hover : (C.yF ≫ pullback.fst _ _) ≫ Xo.s =
      spMap ((algebraMap ℂ ℂ⸨X⸩).comp (bF.comp (IntermediateField.inclusion c.le).toRingHom)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.yF_over, ← spMap_comp]
  have hrat : C.Φ.Rational := GlobalTheory.ConstRational.rational L₁ L₂ E H D l Xo Λ.A _ _ C.Φ laA laM hfin hover levA levM
  obtain ⟨Γ⟩ := GlobalTheory.T.exists_germs_localRing_convergent_divisible.1
  obtain ⟨Ψ⟩ := GlobalTheory.ArcPts.Special.specPts_nonempty L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ _ Xo.s _ hover hfin hrat
  obtain ⟨lin, cst, hfac, hEF⟩ := GlobalTheory.ArcPts.exists_isFactor _ Λ.A
  obtain ⟨T₁, hT₁, hol, hfib⟩ :=
    GlobalTheory.SpecFibre.specPts_isFibAt L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat lin cst hfac
  obtain ⟨TA, -, hlA⟩ := GlobalTheory.SpecLevel.level_on_fibre L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat l.A
  obtain ⟨TM, -, hlM⟩ := GlobalTheory.SpecLevel.level_on_fibre L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat l.M
  have hdim := GlobalTheory.ArcPts.finrank_V_eq L₁ L₂ E H D l c O β _ a Λ g ty hty hrz
  have hol' : IsHolTo {w : ℂ | max T₁ (max TA TM) < w.im} Ψ.yw := isHolTo_halfPlane_mono (le_max_left _ _) hol
  obtain ⟨K, -⟩ := GlobalTheory.ArcPts.exists_cmp L₁ L₂ E H D l Xo _ g ty Fu Λ.A lin cst (max T₁ (max TA TM)) Ψ.yw Ψ.pi Ψ.fr laA laM
    rfl hEF hdim hol' (by
      intro w hw
      simp only [max_lt_iff] at hw
      obtain ⟨h₁, h₂, h₃⟩ := hw
      refine ⟨?_, hfib w h₁, fun hs => ⟨fun v => hlA w h₂ hs (hfib w h₁).per _ _ ?_ (levA v),
        fun v hv => hlM w h₃ hs (hfib w h₁).per _ _ ?_ (levM v hv)⟩⟩
      · rw [Ψ.yw_eq w (hT₁.trans_lt h₁)]
        exact over_of_generic _ _ _ _ _ (by rw [Ψ.yT_gen]; exact hover)
      · rw [← map_nsmul_eq_pow _ Xo.univ.etaA_add, Xo.univ.etaA_ker]
      · rw [← map_nsmul_eq_pow _ Xo.univ.eta_add, Xo.univ.eta_ker _ (nsmul_mem v)])
  exact GlobalTheory.ArcPts.nonempty_holArc L₁ L₂ E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hrat hA hM lin cst T₁ hfib

end GlobalTheory.HolomorphicArc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicDegenerationArcOfUniformisationStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.holomorphic_degenerationArc_of_uniformisation : ReciprocityTheory.ChartRestriction.G.Out.Laws → ReciprocityTheory.ChartRestriction.G.Out.Laws2 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition := by
  first | exact @GlobalTheory.HolomorphicArc.main | exact GlobalTheory.HolomorphicArc.main | (intros; apply GlobalTheory.HolomorphicArc.main <;> assumption)
end
end
