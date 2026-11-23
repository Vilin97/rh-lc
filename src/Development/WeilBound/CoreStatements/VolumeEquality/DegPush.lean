module

public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealAgreementStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerProportionalStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotalStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushCentre
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDim
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFib
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibLink
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankAdjoinVarsField
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushLat
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMap
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMass
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMuLink
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushNumEq
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPF
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPullB
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTest
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTestA
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushUnit

-- Source module: Development.WeilBound.CoreStatements.VolumeEquality.DegPushAsm

section

@[expose] public section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

section

variable {Ω : Type} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)]

theorem asm_vdeg_join_inl (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a (0 : K' → ℤ)) = vdeg O y a := by
  unfold vdeg
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one]
  rfl

theorem asm_vdeg_join_inr (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim (0 : K → ℤ) a) = vdeg O y' a := by
  unfold vdeg
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
  rfl

end

theorem degPush_of (hEq : NumEq) (hPF : GeoPF) (hFib : FibNum) (hTr : TrdegU) (hRel : TestRelabel) (hTest : GeoTest)
    (hMap : NumMap) (hMass : MuMass) (hJoin : FieldJoin) (hIso : GenIso) (hFL : FibLink) (hML : MuLink) : DegPush := by
  classical
  obtain ⟨U, hU⟩ := hFib
  refine ⟨fun f p q => if Top.testDeg (Fin f) (p + q) p / U f p q = 0 then 1 else Top.testDeg (Fin f) (p + q) p / U f p q,
    fun f p q => ?_, ?_⟩
  · beta_reduce
    split_ifs with h
    · exact one_ne_zero
    · exact h
  intro _ hProp _ hG hInt E _ _ _ _ H D Xo l c Y _ T o II hY hX hII hp hq hqp a K _ J _ Ω _ _ W _ _ Dc Hd Or eb es _ _ eS eg
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have : Nonempty (CMType H) := (GlobalTheory.T.cm_host_rank_bounds E H).2.1
  have hT : T.Proportional := GlobalTheory.T.real_tower_proportional hProp hIn II hII _ _ T _ (GlobalTheory.T.good_tower_real_agreement hG E H D Xo l c Y T o II hY hX hII hp hq)
  have htd : 0 < Top.testDeg (CMType H) (D.p + D.q) D.p := (GlobalTheory.T.test_polynomial_shift_total (CMType H) (D.p + D.q) D.p hp (by omega)).2.1
  have eg' : genPt Or.𝔐.ξ₀ = genPt (o.Or 2 a).𝔐.ξ₀ := by
    have g1 := congrArg (fun f => f (IsLocalRing.closedPoint _)) ((o.Or 2 a).g_over.symm.trans (o.Or 2 a).𝔐.fn_over)
    rw [eg]
    exact ((congrArg (fun x => (o.Fx a).ξf x) (Subsingleton.elim (α := PrimeSpectrum (o.Fx a).Ωf) _ _)).trans g1).trans
      (congrArg (fun x => (o.Or 2 a).𝔐.ξ₀ x) (Subsingleton.elim (α := PrimeSpectrum (o.Or 2 a).𝔐.Ω₀) _ _))
  have hvol := hT.1 a
  obtain ⟨M, 𝔐', Fl, e, hδ, hlines, eg', hprop⟩ : ∃ (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐' : HodgeCpt Y (o.S 2) M.y)
      (Fl : 𝔐'.Flag) (e : RootIx D → M.Ω), M.δ = Module.finrank ℚ c.F * Fl.deg ∧ Fl.RootLines M.xdeg e ∧
      genPt Or.𝔐.ξ₀ = genPt 𝔐'.ξ₀ ∧
      M.geoFun (Top.toA (Top.muSmall D.p ^ Top.dimX (CMType H) (D.p + D.q) D.p * Top.fibClass D.p)) = T.vol a *
        Top.degFl (Top.muSmall D.p ^ Top.dimX (CMType H) (D.p + D.q) D.p * Top.fibClass D.p : Top.RP (CMType H) (D.p + D.q)) :=
    ⟨_, _, _, _, (o.Or 2 a).δ_eq, (o.Or 2 a).lines, eg', hT.2.1 2 a _⟩
  obtain ⟨ψ₀, hψ₀⟩ := hIso _ _ _ _ _ Or.𝔐.gen₀ 𝔐'.gen₀ eg'
  let ψ : 𝔐'.Ω₀ →+* Ω := Or.𝔐.fn.comp ψ₀.toRingHom
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates Or.𝔐.ξ 𝔐'.ξ₀ Or.𝔐.f ψ := by
    have h := Or.𝔐.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at h ⊢
    rw [h, hψ₀, ← Category.assoc, ← Spec.map_comp]
    rfl
  let _ : Algebra 𝔐'.Ω₀ Ω := ψ.toAlgebra
  let _ : Algebra 𝔐'.Ω₀ M.Ω := 𝔐'.fn.toAlgebra
  have hdeg : Module.finrank 𝔐'.Ω₀ Ω = Or.deg := by
    let _ := Or.𝔐.fn.toAlgebra
    rw [← Or.cover.2]
    exact Algebra.finrank_eq_of_equiv_equiv ψ₀ (RingEquiv.refl Ω) rfl
  obtain ⟨b, u, hb, -, -, -, u1, u0, hfl, hai, hd0, hd⟩ := Fl.generic
  obtain ⟨Ω₃, _, _, i, d, n₂, hi, hu, hn, hn0, hnd⟩ := hJoin 𝔐'.Ω₀ Ω M.Ω _ _ u Fl.deg Or.deg ⟨u1, u0, hai, hd0, hd⟩ Or.cover.1 hdeg
  have : CharZero Ω := algebraRat.charZero Ω
  have : CharZero Ω₃ := charZero_of_injective_algebraMap (algebraMap Ω Ω₃).injective
  have : CharZero M.Ω := i.charZero
  let ee := (Fintype.equivFin (PairIx (CMType H) D.p D.q)).symm
  obtain ⟨hcount, htest⟩ := hTest hIn (CMType H) D.p D.q M Dc.n _ ee hqp Or.n_eq
  obtain ⟨hM1, hM2, hM3, -⟩ := hMap M.Ω Ω₃ i _ _ M.y _ M.birational (hcount ▸ M.arith) (hn ▸ hn0)
  have hP : IsPt Ω (fun x => i (M.y x)) _ := ⟨hM1.1, hM2 Ω, hTr _ _ _ Ω Ω₃ _ d hu⟩
  obtain ⟨hJ1, hJ2⟩ := hPF hIn II hII Ω Ω₃ _ _ _ _ Dc.y (fun x => i (M.y x)) Dc.n _ (fun _ => Hd.aMu)
    (fun j => fibDeg M.xdeg (ee j)) Dc.birational Dc.arith hP
  have hF := hU _ _ _ Ω Ω₃ _ _ _ _ d _ M.xdeg ee hu hP
    (hFL E H D l _ c Y _ _ _ _ _ 𝔐' Fl _ e b u Ω Ω₃ i hlines hb u1 u0 hfl fun a => ⟨ψ a, (RingHom.congr_fun hi a).symm⟩)
  have hμ := hML E H D Xo l c Y _ _ _ _ _ 𝔐' Fl _ e II K J Ω W Dc Hd _ Or ψ Ω₃ (algebraMap Ω Ω₃) i hlines eb es eS hdom hi.symm
  have hE := hEq ℚ Ω₃ _ _ _ _ _ _ _
    (Fin.append (fun _ : Fin Dc.n => muDeg M.xdeg) fun j => fibDeg M.xdeg (ee j))
    (Fin.append (fun _ : Fin Dc.n => Sum.elim Hd.aMu (0 : M.K → ℤ)) fun j => Sum.elim (0 : K → ℤ) (fibDeg M.xdeg (ee j)))
    hM1 hJ1 fun j => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [Fin.append_left, ValEq, asm_vdeg_join_inl] using hμ
      · refine ⟨1, one_ne_zero, fun O _ => ?_⟩
        simp only [Fin.append_right, asm_vdeg_join_inr, map_one, one_mul]
  have hG1 := (hMap Ω Ω (RingHom.id Ω) _ _ Dc.y Dc.n Dc.birational Dc.arith (by
    rw [show (RingHom.id Ω).fieldRange = ⊤ from RingHom.fieldRange_eq_top_iff.2 Function.surjective_id]
    have : Module.Finite (⊤ : Subfield Ω) Ω :=
      Module.Finite.of_surjective (Algebra.linearMap (⊤ : Subfield Ω) Ω) fun x => ⟨⟨x, trivial⟩, rfl⟩
    exact Module.finrank_pos)).2.2.2 Hd.aMu
  rw [hM3, hJ2, hF, hG1, hn] at hE
  have hE' := congrArg (Int.cast : ℤ → ℝ) hE
  push_cast at hE'
  rw [← htest, ← hMass hG hInt E H D Xo l c Y II K J Ω W Dc Hd _ Or hII, hprop, hδ] at hE'
  have hnd' : (n₂ : ℝ) * Fl.deg = d * Or.deg := by exact_mod_cast hnd
  have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hu.2.2.2.1.ne'
  have := c.fin
  have hFpos : (0 : ℝ) < Module.finrank ℚ c.F := Nat.cast_pos.2 Module.finrank_pos
  have hOpos : (0 : ℝ) < Or.deg := Nat.cast_pos.2 Or.cover.1
  have key : Top.testDeg (CMType H) (D.p + D.q) D.p * Or.deg * Module.finrank ℚ c.F * T.vol a =
      U (Fintype.card (CMType H)) D.p D.q * degMu Hd := by
    apply mul_left_cancel₀ hdpos
    unfold Top.testDeg
    push_cast at hE'
    linear_combination hE' - (Module.finrank ℚ c.F * T.vol a *
      Top.degFl (Top.muSmall D.p ^ Top.dimX (CMType H) (D.p + D.q) D.p * Top.fibClass D.p : Top.RP (CMType H) (D.p + D.q))) * hnd'
  have hU0 : (U (Fintype.card (CMType H)) D.p D.q : ℝ) ≠ 0 := fun h => by
    rw [h, zero_mul] at key
    exact (mul_pos (mul_pos (mul_pos htd hOpos) hFpos) hvol).ne' key
  have hr := hRel (CMType H) (D.p + D.q) D.p
  have hr' : Top.testDeg (Fin (Fintype.card (CMType H))) (D.p + D.q) D.p = Top.testDeg (CMType H) (D.p + D.q) D.p := by
    rw [hr]
  simp only [hr']
  rw [if_neg (div_ne_zero htd.ne' hU0)]
  field_simp
  linear_combination -key

end SheetDecomposition
end
end
end

-- Source module: Development.WeilBound.CoreStatements.VolumeEquality.DegPushJoin

section

@[expose] public section

noncomputable section

namespace SheetDecomposition

open scoped TensorProduct

namespace Join

theorem tower {P Ω : Type} [Field P] [Field Ω] (φ : P →+* Ω) (K₀ : Subfield P) :
    Module.finrank (K₀.map φ) Ω = Module.finrank K₀ P * Module.finrank φ.fieldRange Ω := by
  letI : Algebra P Ω := φ.toAlgebra
  letI : Algebra K₀ Ω := (φ.comp K₀.subtype).toAlgebra
  haveI : IsScalarTower K₀ P Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : Module.finrank P Ω = Module.finrank φ.fieldRange Ω :=
    Algebra.finrank_eq_of_equiv_equiv φ.rangeRestrictFieldEquiv (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)
  have h2 : Module.finrank K₀ Ω = Module.finrank (K₀.map φ) Ω :=
    Algebra.finrank_eq_of_equiv_equiv (K₀.toSubring.equivMapOfInjective φ φ.injective) (RingEquiv.refl Ω)
      (RingHom.ext fun _ => rfl)
  rw [← h1, ← h2, Module.finrank_mul_finrank]

theorem finrank_congr {Ω : Type} [Field Ω] {A B : Subfield Ω} (h : A = B) : Module.finrank A Ω = Module.finrank B Ω := by
  subst h; rfl

theorem map_adjoin {F P Ω : Type} [Field F] [Field P] [Field Ω] [Algebra F P] [Algebra F Ω] (φ : P →+* Ω)
    (hφ : φ.comp (algebraMap F P) = algebraMap F Ω) {I : Type} (w : I → P) :
    (IntermediateField.adjoin F (Set.range w)).toSubfield.map φ =
      (IntermediateField.adjoin F (Set.range fun q => φ (w q))).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, RingHom.map_field_closure, Set.image_union,
    ← Set.range_comp, ← Set.range_comp, ← hφ]
  rfl

theorem core (F A B : Type) [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B] {I : Type} (w : I → B) (d₂ e : ℕ)
    (hw : AlgebraicIndependent F w) (hd : 0 < d₂) (hB : Module.finrank (IntermediateField.adjoin F (Set.range w)) B = d₂)
    (he : 0 < e) (hA : Module.finrank F A = e) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra A Ω) (i : B →+* Ω) (d n : ℕ),
      i.comp (algebraMap F B) = (algebraMap A Ω).comp (algebraMap F A) ∧ AlgebraicIndependent A (fun q => i (w q)) ∧ 0 < d ∧
      Module.finrank (IntermediateField.adjoin A (Set.range fun q => i (w q))) Ω = d ∧
      Module.finrank i.fieldRange Ω = n ∧ 0 < n ∧ n * d₂ = d * e := by
  haveI : FiniteDimensional F A := Module.finite_of_finrank_pos (hA ▸ he)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (B ⊗[F] A)
  letI : Field ((B ⊗[F] A) ⧸ m) := Ideal.Quotient.field m
  let j : A →ₐ[F] ((B ⊗[F] A) ⧸ m) := (Ideal.Quotient.mkₐ F m).comp Algebra.TensorProduct.includeRight
  letI : Algebra A ((B ⊗[F] A) ⧸ m) := j.toRingHom.toAlgebra
  haveI : IsScalarTower F A ((B ⊗[F] A) ⧸ m) := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Module.Finite B ((B ⊗[F] A) ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ B m).toLinearMap (Ideal.Quotient.mkₐ_surjective B m)
  let Ω := ((B ⊗[F] A) ⧸ m)
  let i : B →+* Ω := algebraMap B Ω
  have hi : i.comp (algebraMap F B) = algebraMap F Ω := (IsScalarTower.algebraMap_eq F B Ω).symm
  have hx0 : AlgebraicIndependent F (fun q => i (w q)) :=
    hw.map' (f := IsScalarTower.toAlgHom F B Ω) (algebraMap B Ω).injective
  have hx : AlgebraicIndependent A (fun q => i (w q)) := hx0.extendScalars A
  have hn : 0 < Module.finrank i.fieldRange Ω := by
    rw [← Algebra.finrank_eq_of_equiv_equiv i.rangeRestrictFieldEquiv (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)]
    exact Module.finrank_pos
  have t1 := tower i (IntermediateField.adjoin F (Set.range w)).toSubfield
  rw [finrank_congr (map_adjoin i hi w)] at t1
  let P := FractionRing (MvPolynomial I A)
  let φ : P →+* Ω := (IntermediateField.adjoin A (Set.range fun q => i (w q))).val.toRingHom.comp hx.aevalEquivField.toRingEquiv.toRingHom
  letI : Algebra F P := ((algebraMap A P).comp (algebraMap F A)).toAlgebra
  have hφA : ∀ a, φ (algebraMap A P a) = algebraMap A Ω a := fun a => congrArg Subtype.val (hx.aevalEquivField.commutes a)
  have hφ : φ.comp (algebraMap F P) = algebraMap F Ω := RingHom.ext fun a =>
    (hφA _).trans (IsScalarTower.algebraMap_apply F A Ω a).symm
  have hX : (fun q => φ (algebraMap (MvPolynomial I A) P (MvPolynomial.X q))) = fun q => i (w q) := funext fun q =>
    (hx.aevalEquivField_algebraMap_apply_coe _).trans (MvPolynomial.aeval_X _ q)
  have hr : φ.fieldRange = (IntermediateField.adjoin A (Set.range fun q => i (w q))).toSubfield := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (hx.aevalEquivField y).2
    · intro hz
      exact ⟨hx.aevalEquivField.symm ⟨z, hz⟩, congrArg Subtype.val (hx.aevalEquivField.apply_symm_apply ⟨z, hz⟩)⟩
  have t2 := tower φ (IntermediateField.adjoin F (Set.range fun q => algebraMap (MvPolynomial I A) P (MvPolynomial.X q))).toSubfield
  rw [finrank_congr (map_adjoin φ hφ _), hX, finrank_congr hr] at t2
  have t3 := GlobalTheory.CompanionTheory.FieldDeg.finrank_fraction_over_adjoin_X_eq F A I rfl
  have key : d₂ * Module.finrank i.fieldRange Ω =
      e * Module.finrank (IntermediateField.adjoin A (Set.range fun q => i (w q))) Ω := by
    rw [← hB, ← hA, ← t3]
    exact t1.symm.trans t2
  refine ⟨Ω, inferInstance, inferInstance, i, _, _, hi.trans (IsScalarTower.algebraMap_eq F A Ω), hx, ?_, rfl, rfl, hn, ?_⟩
  · refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, mul_zero] at key
    exact (Nat.mul_pos hd hn).ne' key
  · rw [mul_comm, key, mul_comm]

theorem adjoin_entries (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {S : Type} {r : S → ℕ}
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1) (h0 : ∀ s l m, l < m → u s l m = 0) :
    IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin k
        (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
  · rintro _ ⟨⟨s, l, m⟩, rfl⟩
    show u s l m ∈ _
    rcases lt_trichotomy l m with h | rfl | h
    · rw [h0 s l m h]; exact zero_mem _
    · rw [h1]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, ⟨(l, m), h⟩⟩, rfl⟩
  · rintro _ ⟨⟨s, lm, h⟩, rfl⟩
    exact ⟨⟨s, lm⟩, rfl⟩

end Join

theorem fieldJoin : FieldJoin := by
  intro Ω₀ Ω₁ Ω₂ _ _ _ _ _ S _ r u d₂ e ⟨h1, h0, hi, hd, hf⟩ he hA
  rw [Join.adjoin_entries Ω₀ u h1 h0] at hf
  obtain ⟨Ω, _, _, i, d, n, a1, a2, a3, a4, a5, a6, a7⟩ := Join.core Ω₀ Ω₁ Ω₂ _ d₂ e hi hd hf he hA
  have g1 : ∀ s m, (u s).map i m m = 1 := fun s m => by simp [h1]
  have g0 : ∀ s l m, l < m → (u s).map i l m = 0 := fun s l m h => by simp [h0 s l m h]
  refine ⟨Ω, inferInstance, inferInstance, i, d, n, a1, ⟨g1, g0, a2, a3, ?_⟩, a5, a6, a7⟩
  rw [Join.adjoin_entries Ω₁ (fun s => (u s).map i) g1 g0]
  exact a4

end SheetDecomposition
end
end
end

-- Source module: Development.WeilBound.CoreStatements.VolumeEquality.DegPush

section

@[expose] public section

namespace SheetDecomposition

theorem degPush : DegPush :=
  have hEq : NumEq := numEq ptDim numPull (unitZero ptDim)
  degPush_of hEq (geoPF ptDim) (fibNum hEq) trdegU testRelabel geoTest numMap muMass fieldJoin genIso
    (fibLink chartVal centre coordLat) (muLink chartVal centre coordLat)

end SheetDecomposition
end
end
