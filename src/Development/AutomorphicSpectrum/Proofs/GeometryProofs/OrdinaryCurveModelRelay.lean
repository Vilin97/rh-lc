module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtAfTypeMain
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelHodgeRelayStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModelsStatement
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ValCastSub
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsCmTypeEmbedding
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsDualFamily
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsUnitOfVal
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelMem
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsIntegrallyClosedOfDenomBis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NatCastSmulMemHtLat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointHTOfFarguesHodgeTateStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointsDefinedGenericStatement
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLat
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatTest
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ChartMatrices
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceDifferentialsExist
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestOrderSections
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Typed
import Mathlib.Algebra.Order.Star.Real
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsDualOf

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ReducesAtOfWithE

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

open GlobalTheory.CompanionTheory.Ar.HT PositivityTheory.Xgn.TestGroupPoint.Par

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]

def ReducesAt (D : HTChart A K c p R N Ω) (κ : A) (C O : Type) [Field C] [CommRing O] [Algebra O C] [Algebra A O] :
    Prop :=
  ∃ (V Ω' : Type) (_ : AddCommGroup V) (_ : Module C V) (_ : Module O V) (_ : IsScalarTower O C V)
    (_ : AddCommGroup Ω') (_ : Module C Ω') (_ : Module O Ω') (_ : IsScalarTower O C Ω')
    (P : HTPoint C O c (algebraMap A O κ) N V Ω') (io : D.om →ₛₗ[algebraMap A O] Ω'),
    D.ReducesTo (algebraMap A O) P io

theorem reducesAt_of_withE [NeZero (p ^ R)] (D : HTChart A K c p R N Ω)
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (alt adj hs hi) (a : ℕ) (ha : a.Coprime p)
    (he : ∀ x y, D.e x y = (a : ZMod (p ^ R)) * e x y) (κ : A) {C O : Type} [Field C] [CommRing O] [Algebra O C]
    [Algebra A O] {v : Valuation C NNReal} (hv : v.Integers O) (hp : v (p : C) < 1)
    (h : ReducesAt (withE D e alt adj hs hi) κ C O) : ReducesAt D κ C O := by
  obtain ⟨V, Ω', j1, j2, j3, j4, j5, j6, j7, j8, P, io, hr⟩ := h
  obtain ⟨b, hb⟩ := isUnit_of_coprime hv (by rwa [map_natCast]) ha
  refine ⟨V, Ω', j1, j2, j3, j4, j5, j6, j7, j8, scalePt P b, io,
    ⟨hr.span_eq, hr.rank_eq, hr.lin, hr.ht_eq, fun x y => ?_⟩⟩
  obtain ⟨z, hz⟩ := hr.e_eq x y
  have h1 : ((D.e x y).val : O) + (p : O) ^ R * ((a * (e x y).val / p ^ R : ℕ) : O) = (a : O) * ((e x y).val : O) := by
    have h0 : (D.e x y).val = (a * (e x y).val) % p ^ R := by
      rw [he, ← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [h0]
    exact_mod_cast congrArg (Nat.cast : ℕ → O) (Nat.mod_add_div (a * (e x y).val) (p ^ R))
  refine ⟨((a * (e x y).val / p ^ R : ℕ) : O) + a * z, ?_⟩
  change algebraMap O C (b : O) • P.e (P.tate x) (P.tate y) = _
  rw [hz, smul_eq_mul, ← map_mul, hb]
  congr 1
  change (a : O) * (((e x y).val : O) + (p : O) ^ R * z) = _
  linear_combination -h1

end Chart

open TensorProduct in
theorem reducesAt_of : PointHT → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (Dc : HTChart R K (IsCMField.complexConj E).toRingEquiv p n (D.p + D.q) Ω) (u : Fin (D.p + D.q) → D.La) (hu : IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (x : Sp R ⟶ S) (Γ₀ : QFGroup R (LevGrp D.La p n)) (i : Γ₀.G.left ⟶ t.G.left) (hi : Γ₀.IsTorsionAlong t.G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel t.G x L) (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf t.act.act ρ) (j : Module.Dual R L →ₗ[R] Ω) (hj : IsBaseChange K j) (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p n) (ζ₀ : Rˣ) (κ : R), IsHTChartOf Dc Γ₀ i M ρ j π ζ₀ → (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) → (∀ z z', Dc.e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) → 2 * Module.finrank R L = Module.finrank ℤ D.La → IsProper (Limits.pullback.snd t.G.hom ((BT.genPt R).hom ≫ x)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing R →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ (BT.genPt R).hom ≫ x) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ (p ^ n) : k) = f (algebraMap R _ (ζ₀ : R)) ∧ ∀ a, (I.ev (p ^ n) a).left = spMap f ≫ (Γ₀.pt (lev p n a)).left ≫ i) → (if p = 2 then κ = 4 else ∃ ζ : R, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → ∀ (C O : Type) [Field C] [IsAlgClosed C] [CharZero C] [CommRing O] [IsDomain O] [Algebra O C] [Algebra R O] (v : Valuation C NNReal), v.Integers O → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : O)}) O → Function.Injective (algebraMap R O) → ReducesAt Dc κ C O := by
  intro hPt E _ _ _ H D p _ R K _ _ _ _ _ _ _ _ n Ω _ _ _ _ Dc u hu S _ t x Γ₀ i hi L _ _ M ρ hρ j hj π ζ₀ κ hc hπ he hrank hprop hTate hκ C O _ _ _ _ _ _ _ v hv hp hO hinj
  obtain ⟨-, -, hIC, -, hAC, -⟩ := PositivityTheory.HtPt.Twhopf.padic_alg p C v O hv hp hO
  haveI := hAC
  haveI := hIC
  have hgk : Function.Injective ((algebraMap O (FractionRing O)).comp (algebraMap R O)) :=
    (IsFractionRing.injective O _).comp hinj
  let f : FractionRing R →+* FractionRing O := IsFractionRing.lift hgk
  have hf : ∀ r, f (algebraMap R _ r) = algebraMap O _ (algebraMap R O r) :=
    fun r => IsFractionRing.lift_algebraMap hgk r
  obtain ⟨I, hI1, hI2⟩ := hTate (FractionRing O) f
  have hz : spMap f ≫ (BT.genPt R).hom ≫ x = (BT.genPt O).hom ≫ spMap (algebraMap R O) ≫ x := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simp only [Over.mk_hom, spMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hf
  obtain ⟨L', iA', iM', P, io, hio⟩ := PositivityTheory.HtPt.Htat.TestPts.reduces_at_point hPt E H D p R K n Ω Dc u hu S t x Γ₀
    i hi L M ρ hρ j hj π ζ₀ κ hc hπ he hrank hprop hκ C O v hv hp hO hinj f hf _ hz I hI1 hI2
  exact ⟨C ⊗[ℤ] D.La, C ⊗[O] Module.Dual O L', inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, P, io, hio⟩


open PositivityTheory.HtPt.Htat in
theorem reducesAt_pack (hF : HT.FarguesHodgeTate) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ) (hd : IsArithVar (mCoordIdeal y) (d + 1)) (hpq : 0 < D.p + D.q) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime] (hpm : (p : A) ∈ m) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k) (hc' : mseg y c' ≠ 0) (P : ChartPack G O c')
    (w : O) (hw : HT.IsCp p (algebraMap O Ω w)) (C O' : Type) [Field C] [IsAlgClosed C] [CharZero C] [CommRing O']
    [IsDomain O'] [Algebra O' C] [Algebra (CR O y c') O'] (v : Valuation C NNReal) (hv : v.Integers O')
    (hvp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O')}) O')
    (hφ : Function.Injective (algebraMap (CR O y c') O')) :
    ReducesAt P.Dh (algebraMap O (CR O y c') w) C O' := by
  obtain ⟨h0, hNoe, hIC, hFr⟩ :=
    chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O c' hc'
  obtain ⟨-, hN, hprop, hTa, hrk, -, -⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS
    (zp Ω p) (mem_range_zp Ω p)
  have hp := (Fact.out : p.Prime)
  have hn : p ^ 𝔐.R p ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero (p ^ 𝔐.R p) := ⟨hn⟩
  have hR : 1 ≤ 𝔐.R p := le_trans (by norm_num) (𝔐.R_ge p hpS)
  have hinj : Function.Injective (algebraMap (CR O y c') Ω) := IsFractionRing.injective _ _
  haveI : CharZero (CR O y c') := (algebraMap (CR O y c') Ω).charZero
  obtain ⟨ev, ζ₀, hev⟩ := exists_isParam D 𝔐.t 𝔐.ξ GlobalTheory.T.torsion_points_defined_generic (p ^ 𝔐.R p) (Nat.pos_of_ne_zero hn) hpq hprop
    (𝔐.tors p hpS) hTa
  obtain ⟨u, hu, huz⟩ := exists_coords D 𝔐.t 𝔐.ξ p (𝔐.R p) hR hev G.t₂.pt G.t₂.onto G.t₂.lin
  obtain ⟨π, e, hπ, he, hdec, hsurj, hker, halt, hadj, hes, hei⟩ :=
    exists_levPairing (HT.cmConj E) p (𝔐.R p) D.EF u hu
  obtain ⟨b, hb⟩ := exists_mulEquiv π (qhom (D.p + D.q) (p ^ 𝔐.R p)) hsurj (qhom_surj _ _)
    (fun z => (hker z.toAdd).trans (qhom_eq_one _ _ z.toAdd).symm)
  have hζ₀ : IsPrimitiveRoot (ζ₀ : Ω) (p ^ 𝔐.R p) := IsPrimitiveRoot.coe_units_iff.2 hev.prim
  obtain ⟨a, -, hac, haζ⟩ := (G.ζ_prim.isPrimitiveRoot_iff).1 hζ₀
  have hap : a.Coprime p := Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) hac
  have hee : ∀ x x', G.e x x' = (a : ZMod (p ^ 𝔐.R p)) * e x x' := by
    intro x x'
    let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω _
    let ψ := bcPt 𝔐.ξ i _ rfl
    let cc : (AlgebraicClosure Ω)ˣ :=
      Units.map i.toMonoidHom (ζ₀ ^ D.EF (∑ k, x k • u k) (∑ k, x' k • u k))
    have h1 := (hev.weil (∑ k, x k • u k) (∑ k, x' k • u k) _ i (ψ ≫ ev _) (ψ ≫ ev _) cc rfl rfl).2 rfl
    have h2 := (G.weil x x' _ i _ _ cc (by rw [← huz]; rfl) (by rw [← huz]; rfl)).1 h1
    have h3 : ((ζ₀ ^ D.EF (∑ k, x k • u k) (∑ k, x' k • u k) : Ωˣ) : Ω) = G.ζ ^ (G.e x x').val := i.injective h2
    rw [← pow_val_intCast ζ₀ _ hev.prim.pow_eq_one, ← he, Units.val_pow_eq_pow_val, ← haζ,
      ← pow_val_mul _ _ G.ζ_prim.pow_eq_one] at h3
    exact ZMod.val_injective _ (G.ζ_prim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3.symm)
  refine reducesAt_of_withE P.Dh e halt hadj hes hei a hap (fun x x' => by rw [P.Dh_e, hee]) _ hv hvp ?_
  have hζ1 : P.ζ ^ (p ^ 𝔐.R p) = 1 := Units.ext (hinj (by
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one]
    exact (congrArg (· ^ (p ^ 𝔐.R p)) P.ζ_eq).trans G.ζ_prim.pow_eq_one))
  have hζa : algebraMap (CR O y c') Ω ((P.ζ ^ a : (CR O y c')ˣ) : CR O y c') = ζ₀ := by
    rw [Units.val_pow_eq_pow_val, map_pow, ← haζ]
    exact congrArg (· ^ a) P.ζ_eq
  let κ : FractionRing (CR O y c') ≃+* Ω := (FractionRing.algEquiv (CR O y c') Ω).toRingEquiv
  have hκ : ∀ r, κ (algebraMap (CR O y c') _ r) = algebraMap (CR O y c') Ω r :=
    (FractionRing.algEquiv (CR O y c') Ω).commutes
  have hκf : fracToField (CR O y c') = κ.toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (CR O y c'))
    ext r
    exact (IsFractionRing.lift_algebraMap (g := algebraMap (CR O y c') Ω) hinj r).trans (hκ r).symm
  have hq : spMap κ.symm.toRingHom ≫ 𝔐.ξ = (BT.genPt (CR O y c')).hom ≫ P.x := by
    rw [← P.x_gen, ← Category.assoc, ← HTTie.spec_comp]
    congr 3
    ext r
    exact (RingEquiv.symm_apply_eq κ).2 (hκ r).symm
  haveI := P.fin
  refine reducesAt_of (GlobalTheory.T.pointHT_of_fargues_hodge_tate hF) E H D p (CR O y c') Ω (𝔐.R p) _ (withE P.Dh e halt hadj hes hei) u hu 𝔐.X 𝔐.t P.x (relabel P.Γ₂ b) P.i₂
    ⟨P.tors₂.isOver, P.tors₂.mul, P.tors₂.inj, P.tors₂.kernel⟩ P.L P.M P.ρ P.act P.j P.j_bc π (P.ζ ^ a) (algebraMap O (CR O y c') w)
    ⟨P.isHT.1, P.isHT.2.1, fun z => ?_⟩ hπ he ?_ (isProper_of_iso _ 𝔐.ξ _ _ hq) (fun k _ _ f => ?_)
    (cp_descend hinj p (algebraMap O (CR O y c') w) hw) C O' v hv hvp hO hφ
  · obtain ⟨χ, w₀, hχ, hh, s, hs, hHT⟩ := P.isHT.2.2 z
    refine ⟨χ.comp b.toMonoidHom, w₀, fun z' => ?_, hh, s, fun t => hs (b t), hHT⟩
    change χ (b (π _)) = (P.ζ ^ a) ^ (e z z').val
    rw [hb, hχ, P.Dh_e, hee, pow_val_mul _ _ hζ1]
  · rw [← hrk, P.toLi_bc.finrank_eq]
  · have hk : spMap (f.comp κ.symm.toRingHom) ≫ 𝔐.ξ = spMap f ≫ (BT.genPt (CR O y c')).hom ≫ P.x := by
      rw [← hq, Tor.spMap_comp, Category.assoc]
    obtain ⟨I, hz, hI⟩ := hev.tate' D 𝔐.t 𝔐.ξ k _ _ hk
    refine ⟨I, ?_, fun x => ?_⟩
    · rw [hz, ← hζa, ← hκ]
      exact congrArg f (κ.symm_apply_apply _)
    · obtain ⟨z, r, rfl⟩ := hdec x
      have e1 : HT.lev p (𝔐.R p) (∑ k, z k • u k + (p ^ 𝔐.R p) • r) = π (Multiplicative.ofAdd z) := by
        rw [hπ]
        refine congrArg Multiplicative.ofAdd ((Submodule.Quotient.eq _).2 ⟨r, ?_⟩)
        exact (add_sub_cancel_left _ _).symm
      rw [hI, hev.add, (hev.ker _).2 ⟨r, rfl⟩, _root_.mul_one, huz, P.pts₂, e1, hκf]
      change _ = spMap f ≫ (P.Γ₂.pt (b (π _))).left ≫ P.i₂
      rw [hb]
      exact spMap_cancel κ f _

theorem point_data (hF : HT.FarguesHodgeTate) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ) (hd : IsArithVar (mCoordIdeal y) (d + 1)) (hpq : 0 < D.p + D.q) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime] (hpm : (p : A) ∈ m) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k) (hc' : mseg y c' ≠ 0) (P : ChartPack G O c') (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C)
    (w : O) (hw : HT.IsCp p (algebraMap O Ω w)) (hT : IsTestPt p (CR O y c') RC) :
    ∃ (g : ℕ) (io : P.Dh.om →ₛₗ[toRC (CR O y c') RC hT.2.2.2] (Fin g → RC))
      (ev : 𝔐.Li → ((Fin g → C) →ₗ[C] C)) (Hm : Matrix (Fin g) (Ix E (D.p + D.q)) RC)
      (Eg : Matrix (Ix E (D.p + D.q)) (Ix E (D.p + D.q)) RC),
      Submodule.span RC (Set.range io) = ⊤ ∧
      (∀ v (u : P.Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v)) ∧
      Fintype.card (Ix E (D.p + D.q)) = g + g ∧ Egᵀ = -Eg ∧
      (∃ Ei : Matrix (Ix E (D.p + D.q)) (Ix E (D.p + D.q)) RC, Ei * Eg = 1 ∧ Hm * Ei * Hmᵀ = 0) ∧
      (∀ m m', Eg m m' - ((G.e (dl m) (dl m')).val : RC) ∈ Ideal.span {(p : RC)}) ∧
      ∀ m k, Hm k m - io ⟨P.Dh.h (dl m), P.Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)} := by
  obtain ⟨h0, hNoe, hIC, hFr⟩ := chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O c' hc'
  have hC := hT.1
  obtain ⟨v, hv, hvp⟩ := hT.2.1
  haveI : CharZero C := charZero_of_injective_ringHom (algebraMap Ω C).injective
  have hint : v.Integers RC :=
    ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv _).2 hr⟩, rfl⟩⟩
  letI : Algebra (CR O y c') RC := (toRC (CR O y c') RC hT.2.2.2).toAlgebra
  have hφ : Function.Injective (algebraMap (CR O y c') RC) := fun a b h =>
    Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))
  obtain ⟨V, Ω', _, _, _, _, _, _, _, _, Pt, io₀, hr⟩ := reducesAt_pack hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS A m hpm O G c' hc' P w hw C RC v hint hvp hT.2.2.1 hφ
  obtain ⟨g, io, Hm, Eg, h1, h2, h3, h4, h5, h6, h7⟩ :=
    chart_matrices (le_trans (by norm_num) (𝔐.R_ge p hpS)) P.Dh hint Pt io₀ hr
  let f : 𝔐.Li → (P.Dh.om →ₛₗ[algebraMap (CR O y c') RC] C) := fun x =>
    { toFun := fun u => algebraMap Ω C (u.1 x)
      map_add' := fun a b => by rw [Submodule.coe_add, LinearMap.add_apply, map_add (f := _)]
      map_smul' := fun r a => by
        change algebraMap Ω C ((r : Ω) * a.1 x) = algebraMap Ω C (r : Ω) * algebraMap Ω C (a.1 x)
        rw [map_mul] }
  choose ev hev using fun x => h2 (f x)
  refine ⟨g, io, ev, Hm, Eg, h1, fun x u => hev x u, h3, h4, h5, fun m m' => ?_, h7⟩
  rw [← P.Dh_e]
  exact h6 m m'

end PositivityTheory.Xgn.TestGroupPoint
end
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestGroupPointExists

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestGroupPoint

theorem spanOver_ind {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C)
    {r : ℕ} (L : AddSubgroup (Fin r → Ω)) (T : AddSubgroup (Fin r → C)) (hT : ∀ t ∈ RC, ∀ a ∈ T, t • a ∈ T)
    (h : ∀ a ∈ L, (fun k => algebraMap Ω C (a k)) ∈ T) : spanOver RC (bcMap Ω C _ '' L) ≤ T := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨t, ht, _, ⟨a, ha, rfl⟩, rfl⟩
  exact hT t ht _ (h a ha)

theorem mem_spanOver {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C)
    {r : ℕ} (L : AddSubgroup (Fin r → Ω)) {a : Fin r → Ω} (ha : a ∈ L) :
    (fun k => algebraMap Ω C (a k)) ∈ spanOver RC (bcMap Ω C _ '' L) :=
  AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨a, ha, rfl⟩, (one_smul _ _).symm⟩

def smallSub {C : Type} [Field C] (v : Valuation C NNReal) (t : NNReal) {r : ℕ} {I : Type}
    (f : I → ((Fin r → C) →ₗ[C] C)) : AddSubgroup (Fin r → C) where
  carrier := {a | ∀ m, v (f m a) ≤ t}
  add_mem' ha hb m := by rw [map_add (f := _)]; exact v.map_add_le (ha m) (hb m)
  zero_mem' m := by simp
  neg_mem' ha m := by rw [map_neg, Valuation.map_neg]; exact ha m

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a :=
  RingOfIntegers.ext (by rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])

end PositivityTheory.Xgn.TestGroupPoint

open PositivityTheory.Xgn.TestGroupPoint PositivityTheory.HtPt.Sgp in
theorem PositivityTheory.Xgn.test_group_point_exists : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  intro hF _ _ hHD hOC E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd hpq p _ hpS hfree hp2 hdisc b hb φ hφ A _ _ _ m _
    hpm O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σF hO hsec G c' hc' P i hseq hbase C _ _ _ _ RC hT χ hχ _ _ _ v hv hvp
    τ hbm _ _ hW hcl
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hR4 := 𝔐.R_ge p hpS
  obtain ⟨h0, hNoe, hIC, hFr⟩ := Par.chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O c' hc'
  obtain ⟨-, hN, -⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS (Par.zp Ω p) (Par.mem_range_zp Ω p)
  obtain ⟨AA, AW, hAA, hAW, hM, hret, -⟩ := PositivityTheory.Xgn.test_order_sections E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σF hO hsec G c' hc' P i hseq hbase C RC hT χ hχ
  obtain ⟨-, htight⟩ := GlobalTheory.T.arith_variety_model_hodge_relay hHD hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σF hO hsec G c' hc' P i hseq hbase C RC hT χ hχ v hv hvp
  obtain ⟨g, io, ev, Hm, Eg, hio, hev, hcard, hEt, ⟨Ei, hEi, hiso⟩, hE, hH⟩ :=
    point_data hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P C RC w hO.2.2.2.2.2.2.2 hT
  obtain ⟨Dv, hD, hDs, hDch⟩ := exists_der hpS P hT.2.2.2 io
  have hlat := fun t => lattices E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P C RC hdisc
    hT.2.2.2 io ev hio hev t (b t) (hb t).1 (hb t).2
  haveI := hT.1
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap Ω C).injective
  have hint : v.Integers RC := ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv _).2 hr⟩, rfl⟩⟩
  obtain ⟨φN, hφN⟩ := exists_phiN E (D.p + D.q) p
  have hζ : IsPrimitiveRoot (algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1))) p :=
    (G.ζ_prim.pow (pow_pos hpp.pos _) (by rw [← pow_succ, Nat.sub_add_cancel (by omega)])).map_of_injective
      (algebraMap Ω C).injective
  let ih : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin g → RC) := io.toAddMonoidHom.comp (P.Dh.h.codRestrict P.Dh.om P.Dh.h_mem)
  obtain ⟨cp, hcp, k0, k1, k2, k3, k4⟩ := core_pull hint hvp hp2 φN hφN AA _ hAA htight hcard
    (dvd_pow_self p (show 𝔐.R p ≠ 0 by omega)) G.e hζ (kernel_mem hpS P hT) Dv hD (Set.range io) hio
    (by rintro _ ⟨u, rfl⟩; exact hDs u) ih hDch Hm Eg Ei hEt hEi hiso hE hH
  obtain ⟨σ, hσ, hσs, -⟩ := PositivityTheory.Xgn.exists_cm_type_embedding E H D l Xo c O₀ β Y S Ω K J y 𝔐 (e τ)
  obtain ⟨hσO, x₀, hx₀, o₀, ho₀⟩ := PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hdisc A m hpm O σ
  have hOC' : ∀ o : O, algebraMap Ω C (algebraMap O Ω o) = algebraMap O C o := fun o =>
    (IsScalarTower.algebraMap_apply O Ω C o).symm
  obtain ⟨σ', s, hσ', hs, hdu⟩ := exists_dualOf (R := RC) (C := C) Subtype.val_injective ((algebraMap Ω C).comp σ)
    (fun a => by
      obtain ⟨o, ho⟩ := hσO a
      exact ⟨algebraMap O RC o, by rw [RingHom.comp_apply, ← ho, hOC']; rfl⟩)
    (fun k => by
      obtain ⟨z, hz⟩ := HT.exists_different_mul_dualInt E x₀ hx₀ k
      obtain ⟨o, ho⟩ := hσO z
      refine ⟨algebraMap O RC (o₀ * o), ?_⟩
      have : algebraMap O Ω (o₀ * o) = σ (HT.dualInt E k) := by
        rw [map_mul, ho, hz, map_mul, ← _root_.mul_assoc, ho₀, _root_.one_mul]
      rw [RingHom.comp_apply, ← this, hOC']; rfl)
  obtain ⟨χ', hχ', hcong⟩ := chi_cong p RC v hv pq sc hsec (σF τ) (χ τ) (hχ τ) σ' fun a => by
    obtain ⟨o, ho, ho'⟩ := hO.2.2.2.2.1 τ a
    exact ⟨o, by rw [← hOC', ho, ← hσ]; exact (hσ' a).symm, ho'⟩
  have hst := afLat_stable hdu φN hφN AA.carrier (fun a f hf => by rw [hAA] at hf ⊢; exact act_mem P a f hf) _
    (mem_pull φN AA)
  have hhh := (pt_af_type_main RC p (ReciprocityTheory.PGsh.Up.hopfPull φN AA).carrier (ReciprocityTheory.PGsh.Up.hopfPull φN AA).le_int
    ((chartD e b pq sc w P i).bc RC) χ' (Subtype.ext (by rw [← hχ', map_zero]; rfl))
    (Subtype.ext (by rw [← hχ', map_one]; rfl))
    (φN.symm.toAddMonoidHom.comp (TestPt.toNAdd sc)) ((TestPt.fromNAdd pq).comp φN.toAddMonoidHom)
    (fun z => by
      change TestPt.fromNAdd pq (φN (φN.symm (TestPt.toNAdd sc z))) = z
      rw [AddEquiv.apply_symm_apply]
      exact funext fun k => hsec.1 (z k))
    (fun h hh => by
      obtain ⟨f, hf, rfl⟩ := (mem_pull φN AA h).1 hh
      refine (mem_pull φN AA _).2 ⟨_, hret f hf, funext fun x => ?_⟩
      change _ = f (φN (φN.symm _))
      rw [AddEquiv.apply_symm_apply]
      rfl)
    (by
      rw [← hM, hAW, TestPt.testOrdW, ← hAA]
      congr 1
      ext f
      constructor
      · rintro ⟨h, hh, rfl⟩
        obtain ⟨f, hf, rfl⟩ := (mem_pull φN AA h).1 hh
        refine ⟨f, hf, funext fun x => ?_⟩
        change _ = f (φN (φN.symm _))
        rw [AddEquiv.apply_symm_apply]
        rfl
      · rintro ⟨f, hf, rfl⟩
        refine ⟨_, (mem_pull φN AA _).2 ⟨f, hf, rfl⟩, funext fun x => ?_⟩
        change f (φN (φN.symm _)) = _
        rw [AddEquiv.apply_symm_apply]
        rfl)
    (Pm _ σ') (Jm _ s) (Pm_mul_Jm hdu) (Pm_cong pq φN hφN χ' hcong) hst).2
  simp only [← hχ'] at hhh
  obtain ⟨u, hu, hwu⟩ := hO.2.2.2.2.2.2.1.2.1
  have hp3 : 2 ≤ p - 1 := by have := hpp.two_le; omega
  have hvw : v (algebraMap O C w) ^ (p - 1) = v (p : C) := by
    rw [← map_pow, ← map_pow, hwu, map_mul, map_mul, map_natCast,
      show v (algebraMap O C u) = 1 from hint.one_of_isUnit (hu.map (algebraMap O RC)), _root_.one_mul]
  have hw1 : v (algebraMap O C w) < 1 := lt_of_not_ge fun h => absurd (hvw ▸ one_le_pow₀ h) (not_le.2 hvp)
  have hw0 : algebraMap O C w ≠ 0 := fun h => by
    rw [h, map_zero, zero_pow (by omega), eq_comm, Valuation.zero_iff] at hvw
    exact Nat.cast_ne_zero.2 hpp.ne_zero hvw
  have hpw : v (p : C) ≤ v (algebraMap O C w) * v (algebraMap O C w) := by
    rw [← hvw, ← sq]
    exact pow_le_pow_of_le_one zero_le hw1.le hp3
  have hWl : ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, algebraMap O C w • a ∈ ((chartD e b pq sc w P i).bc RC).lie τ :=
    fun a ha => spanOver_ind RC _ (divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ))
      (fun t ht a ha => by
        simp only [divLat, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply] at ha ⊢
        rw [smul_comm]
        exact smul_mem_spanOver RC _ ht ha)
      (fun a ha => by
        have h1 : algebraMap O Ω w • a ∈ (chartD e b pq sc w P i).lie τ := (hbase.incl τ).2.1 ha
        have h2 := mem_spanOver RC _ h1
        have e : algebraMap O C w • (fun k => algebraMap Ω C (a k)) =
            fun k => algebraMap Ω C ((algebraMap O Ω w • a) k) := by
          funext k
          change _ = algebraMap Ω C (algebraMap O Ω w * a k)
          rw [map_mul, hOC']
          rfl
        simp only [divLat, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply]
        rw [e]
        exact h2) ha
  have heig : ∀ t a k, 𝔐.ρ a (b t k) = 𝔐.emb t a • b t k := fun t a k => by
    have : b t k ∈ 𝔐.Vgen t := (hb t).2 ▸ Submodule.subset_span ⟨k, rfl⟩
    simp only [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      sub_eq_zero] at this
    exact this a
  refine typed RC v hv (p : C) (algebraMap O C w) hw0 hw1 hpw cp (p : RC)
    ((pow_left_inj₀ zero_le zero_le (by omega)).1 (hcp.trans hvw.symm)) (SubringClass.coe_natCast _ _) _ Hm Eg Ei hEi
    k0 k1 k2 k3 k4 (Pm _ σ') (Jm _ s) (Pm_mul_Jm hdu) hst _ hhh (fun k => ev (b (e τ).swap k)) (fun k => ev (b (e τ) k))
    _ _ _ (hlat (e τ).swap).1 (hlat (e τ)).2
    (spanOver_ind RC _ _ (fun t ht a ha => smul_mem_spanOver RC _ ht ha) fun a ha =>
      mem_spanOver RC _ ((hbase.incl τ).1 ha)) hWl _
    (hq_chart P.Dh 𝔐.ρ H.bar io ev Hm (by omega) P.Dh_act hev hH σ σ' hσ' (b (e τ).swap) fun a k => ?_)
    (TestPt.bcLin C (i τ)) hbm (fun a ha => ?_) hW hcl
  · rw [heig, ← hσs, H.bar_eq, RingHom.comp_apply]
    congr 2
    first
      | exact IsCMField.complexConj_apply_apply E _
      | simp [HT.cmConj]
  · let f : Ix E (D.p + D.q) → ((Fin (labelRk D (e τ)) → C) →ₗ[C] C) := fun m =>
      ∑ m', (Eg m m' : C) • (LinearMap.proj m' ∘ₗ ((Jm _ s).map (algebraMap RC C)).mulVecLin ∘ₗ TestPt.bcLin C (i τ)) +
        ∑ k, ev (b (e τ) k) (fun j => (Hm j m : C)) • LinearMap.proj k
    have hf : ∀ m a, f m a = ∑ m', (Eg m m' : C) * ((Jm _ s).map (algebraMap RC C)).mulVec (TestPt.bcLin C (i τ) a) m' +
        ∑ k, a k * ev (b (e τ) k) fun j => (Hm j m : C) := fun m a => by
      simp only [f, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Matrix.mulVecLin_apply, smul_eq_mul, mul_comm (a _)]
    intro m
    rw [← hf]
    refine spanOver_ind RC _ (smallSub v (v (algebraMap O C w)) f) (fun t ht a ha m => ?_) (fun a ha m => ?_) ha m
    · rw [map_smul, smul_eq_mul, map_mul]
      exact (mul_le_of_le_one_left zero_le ((hv _).1 ht)).trans (ha m)
    · rw [hf, show TestPt.bcLin C (i τ) (fun k => algebraMap Ω C (a k)) = fun l => algebraMap Ω C (i τ a l) from
        funext (bcLin_bc _ _)]
      exact hdual_chart P.Dh 𝔐.ρ H.bar io ev Hm (by omega) P.Dh_act hev hH (bar_bar H)
        (by rw [P.Dh_e]; exact G.adj) Eg (by rw [P.Dh_e]; exact hE) σ σ' hσ' s hs hdu (b (e τ))
        (fun a k => by rw [heig, hσ]) v hv _ hw0 hw1.le hpw a (i τ a)
        (fun l => (hseq τ).1.1 a ha l (Set.mem_univ l)) (M := 𝔐.R p - 2) (by omega) ((hseq τ).2 σ hσ a ha)
        ((hlat (e τ)).2 _ |>.1 (hWl _ (mem_spanOver RC _ ha))) m
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveModelRelay

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.CompanionTheory.Relay.ordinary_curve_model_relay : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  first | exact @PositivityTheory.Xgn.test_group_point_exists | exact PositivityTheory.Xgn.test_group_point_exists
end
end
