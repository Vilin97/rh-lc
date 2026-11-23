module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementS
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLocalModelOverDvrStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIffStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitIntegralGeneratorPrincipalLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralEigenbasisBaseChangeDvrStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralGeneratorAssociatedLocalGeneratorCMLineStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SecTieBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LiftBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasisStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RuleValueIntegralOfSupLatticeValuesNonnegStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationDetLeOneOfEntries
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationLeIffExistsSmulMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralGeneratorBaseChangeValuationRing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem secInt_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), SecBC i 1 x x' s s' → SecInt T m1 m2 s → SecInt T' m1' m2' s' := by
  intro E _ _ _ H Dw l Xo T T' ψ i hψ x x' G G' t t' m1 m2 m1' m2' n n' hx h1 h2 s s' hb
  have isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
      (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
      IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
        gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
    constructor
    · intro h Z r z j k hj hk
      have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
      have a := congrArg (gs r z _) (h (fun _ => j) k)
      exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
          (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
    · intro h (i : PUnit → L.ι) k
      exact fn_ext fun p hp =>
        (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
          (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

  rintro ⟨θ, hθ, w2, σ, θ2, r2, i2, p2, tie⟩
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨wn, gn, rn, -⟩ := n.lin
  obtain ⟨wn', gn', rn', -⟩ := n'.lin
  obtain ⟨w2', g2', r2', -⟩ := m2'.lin
  have Rn : RigIso n wn := ⟨gn, rn⟩
  have Rn' : RigIso n' wn' := ⟨gn', rn'⟩
  have R2' : RigIso m2' w2' := ⟨g2', r2'⟩
  obtain ⟨θ', hθ'⟩ := sec_pull_down ((isGen_iff wn).1 gn) G.t.PP.isLB G'.t.PP.isLB θ
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w2').1 g2') G'.t.PP.isLB t'.PP.isLB θ'
  have nz : ∀ y : Sp T.V, ∃ z : G.t.G.left, G.t.G.hom z = y ∧ z ∈ Out.nonzeroLocus θ := fun y => by
    obtain ⟨b, hb, -⟩ := GlobalTheory.KeyOnPol.exists_generator hS G.pol
    obtain ⟨z, hz, hm⟩ := hb y
    obtain ⟨a, ha, -⟩ := hθ b
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    rw [ha k, Scheme.basicOpen_mul] at hk
    exact ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk.2⟩⟩
  have nz' := SectionBaseChange.fibre_nonzero_of_pull G'.t.PP.isLB hθ' n.cart.1 nz
  refine ⟨θ', SectionBaseChange.generates hS G.pol n.cart.1 G'.t.PP.isLB ⟨wn, gn⟩ θ' nz', w2', σ',
    thfPull G'.t.PP.L m2'.φ θ', R2', ?_, fun _ _ => rfl, ?_⟩
  · refine (isoMaps_iff _ _ _).2 fun Z r z j k hj hk => ?_
    exact (gs_appLE m2'.φ _ _ _ r z (mem_pull.2 hj) _).trans (hσ' Z r z j k hj hk)
  · refine (TieCalc.secTie_baseChange m1 tie i m1' n' s' wn' (thfPull t.PP.L n'.φ σ) σ' hx h1 hb Rn'
      (fun _ _ => rfl)).2 ((isoMaps_iff _ _ _).2 fun Z r z j k hj hk => ?_)
    have hbase : spMap (algebraMap T'.V T'.Fr) ≫ spMap ψ = spMap i ≫ spMap (algebraMap T.V T.Fr) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
    obtain ⟨N, hN⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ n m2'
    have hN' : N.φ = m2'.φ ≫ n.φ := hN
    obtain ⟨wa, ra, Ta⟩ := GlobalTheory.LiftBaseChange.rigIso_comp n m2' N rfl hN' Rn R2'
    obtain ⟨wb, rb, Tb⟩ := GlobalTheory.LiftBaseChange.rigIso_comp m2 n' N hbase (hN'.trans h2) r2 Rn'
    have hp : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m2'.cart.1 G'.ab.proper
    have hab : IsAbelianScheme t'.G := ⟨t'.semi.comm, t'.semi.smooth, hp, t'.semi.geomConnected⟩
    obtain rfl : wa = wb := iso_unique_of_rig GlobalTheory.globalFns_holds t'.G hab t'.PP.isLB G.t.PP.isLB ra.1 rb.1 ra.2 rb.2
    obtain ⟨a, ha⟩ := exists_chart G.t.PP.isLB (m2.φ (n'.φ (r z)))
    obtain ⟨b, hb'⟩ := exists_chart G'.t.PP.isLB (m2'.φ (r z))
    have ha' : n.φ (m2'.φ (r z)) ∈ G.t.PP.L.U a := (congrArg (fun q => q (r z) ∈ G.t.PP.L.U a) h2).mpr ha
    have e1 := hθ' Z (r ≫ m2'.φ) z a b ha' hb'
    have e2 := hσ' Z r z b k hb' hk
    have le : (G.t.PP.L.pull m2.φ).U (fun _ => a) ≤ m2.φ ⁻¹ᵁ G.t.PP.L.U a := fun q hq => mem_pull.1 hq
    have e3 := (isoMaps_iff _ _ _).1 i2 Z (r ≫ n'.φ) z a j ha hj
    rw [p2 (fun _ => a) le, gs_appLE m2.φ _ _ le (r ≫ n'.φ) z (mem_pull.2 ha), Category.assoc, ← h2,
      ← Category.assoc, e1, e2, ← _root_.mul_assoc, ← Units.val_mul, ← Ta Z r z a b k ha' hb' hk,
      Tb Z r z a j k ha hj hk, Units.val_mul, _root_.mul_assoc] at e3
    exact (gs_appLE n'.φ _ _ _ r z (mem_pull.2 hj) _).trans ((Units.mul_right_inj _).1 e3).symm

end GlobalTheory.LamT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralGeneratorBaseChangeValuationRingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.integral_generator_baseChange_valuationRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), SecBC i 1 x x' s s' → SecInt T m1 m2 s → SecInt T' m1' m2' s' := by
  first | exact @GlobalTheory.LamT.secInt_baseChange | exact GlobalTheory.LamT.secInt_baseChange | (intros; apply GlobalTheory.LamT.secInt_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrime

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LocClause

theorem exists_isLocGen {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ∃ c : K, IsLocGen p c I := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer K
  refine ⟨π ^ FractionalIdeal.count K p I, (GlobalTheory.LamF.isLocGen_iff_valuation_eq p _ _).2 ?_⟩
  rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
  simp

theorem map_evalFr {B : Type} {m : B → ℕ} {R S : Type} [CommRing R] [CommRing S] (κ : R →+* S)
    (P : MvPolynomial (FrVar m) R) (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) :
    κ (evalFr P Y) = evalFr (MvPolynomial.map κ P) (fun b => (Y b).map κ) := by
  unfold evalFr
  induction P using MvPolynomial.induction_on <;> simp_all

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem secBC_one_of_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {y' : FrPt Xo c T} (h : FrMap φ y y') : SecBC φ.toRingHom 1 y.x y'.x y.s y'.s := by
  obtain ⟨-, -, pm, h₁, h₂, h₃⟩ := h
  refine ⟨pm, h₁, h₂, fun i hi => Eq.trans (congrArg _ ?_) (h₃ i hi)⟩
  have h1 := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x
    (by simp [spMap]) (by simp [spMap])).2.2.2 1 1 i).2.2
  rw [h1, _root_.one_mul]

theorem evR_scale {S : Type} [Field S] [Algebra c.F S] {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {F : Rul Xo c}
    (hF : F ∈ sec Xo c a n) (s : Sˣ) {y y' : FrPt Xo c S} (h : FrChg (fun _ => 1) (s : S) y y') :
    evR Xo c F y' = (s : S) ^ n * evR Xo c F y := by
  let t : Ix Dw → Sˣ := fun i => i.elim s (fun _ => 1)
  have hb : FrBor t y y' := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp [t], h⟩
  rw [(GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 S inferInstance a n F hF t y y' hb]
  congr 1
  simp [wchar, Fintype.prod_option, t, ex]

theorem integral_of_eq (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr)
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X} :
    letI := io.toAlgebra
    y.x = x → ∀ (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      LieInt T io m1 m2 y.u → SecInt T m1 m2 y.s → Integral T io y := by
  intro h
  subst h
  exact integral_of T io y

theorem secInt_baseChange (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr)
    (hψ : (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr))
    {x x₁ : Sp T.Fr ⟶ Xo.X} {x' x₁' : Sp T'.Fr ⟶ Xo.X} {G : PAT H (Sp T.V)} {G' : PAT H (Sp T'.V)}
    {t : SAB H (Sp T.Fr)} {t' : SAB H (Sp T'.Fr)} (m1 : SABMap t Xo.univ.t x)
    (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x')
    (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ))
    (n' : SABMap t' t (spMap i)) (hx : x' = spMap i ≫ x) (h1 : m1'.φ = n'.φ ≫ m1.φ)
    (h2 : m2'.φ ≫ n.φ = n'.φ ≫ m2.φ) (e : x₁ = x) (e' : x₁' = x') (s : LB.Sec (PPx x₁)) (s' : LB.Sec (PPx x₁'))
    (hs : SecBC i 1 x₁ x₁' s s') (h : SecInt T m1 m2 s) : SecInt T' m1' m2' s' := by
  subst e e'
  exact GlobalTheory.T.integral_generator_baseChange_valuationRing E H Dw l Xo T T' ψ i hψ _ _ G G' t t' m1 m2 m1' m2' n n' hx h1 h2 s s' hs h

theorem integral_baseChange_chg [StarRing (𝓞 E)] (z : CMPt Xo c) (T T' : CDVR) (iK : z.K →+* T.Fr)
    (M : LocMod z T iK) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr)
    (hψ : (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr)) (io : c.F →+* T.Fr) :
    letI := io.toAlgebra
    letI := (i.comp io).toAlgebra
    ∀ (iA : T.Fr →ₐ[c.F] T'.Fr) (y : FrPt Xo c T.Fr) (y' w : FrPt Xo c T'.Fr)
      (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T'.V),
      iA.toRingHom = i → y.x = spMap iK ≫ z.x → LieInt T io M.m1 M.m2 y.u → SecInt T M.m1 M.m2 y.s →
      FrMap iA y y' → (∀ b, IsUnit (X b).det) → FrChg (fun b => (X b).map (algebraMap T'.V T'.Fr)) 1 y' w →
      Integral T' (i.comp io) w := by
  letI := io.toAlgebra
  letI := (i.comp io).toAlgebra
  intro iA y y' w X hi hy hL hS hm hX hw
  obtain ⟨M', n, n', h1, h2⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).2 M T' ψ i hψ
  have hx : spMap (i.comp iK) ≫ z.x = spMap i ≫ spMap iK ≫ z.x := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, Category.assoc]
  have hy' : y'.x = spMap (i.comp iK) ≫ z.x := by rw [hm.1, hi, hy, hx]
  have hL' : LieInt T' (i.comp io) M'.m1 M'.m2 y'.u := by
    have := GlobalTheory.T.integral_eigenbasis_baseChange_dvr E H Dw l Xo c T T' ψ i hψ _ _ M.G M'.G M.t'.t M'.t'.t M.m1 M.m2 M'.m1 M'.m2 n n' hx h1 h2
      io y.u hL
    have hu : y'.u = fun τ k => spMap (Formalism.L2.Pj.dualMap i) ≫ y.u τ k := by
      funext τ k
      rw [hm.2.1 τ k, hi]
    rw [hu]
    exact this
  have hLw : LieInt T' (i.comp io) M'.m1 M'.m2 w.u :=
    (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T' (i.comp io) M'.G.t M'.t'.t _ M'.m1 M'.m2 y' hy').2 hL' X 1 w hX hw
  have hs1 : SecBC i 1 y.x y'.x y.s y'.s := by
    have := secBC_one_of_frMap hm
    rwa [hi] at this
  have hs2 : SecBC i 1 y.x w.x y.s w.s := by
    have := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo _ _ _ i (RingHom.id _) y.x y'.x w.x
      (by rw [hm.1, hi]) (by rw [hw.1]; simp [spMap])).1 1 _ _ _ hs1).1 hw.2.2
    rwa [RingHom.id_comp] at this
  have hwx : w.x = spMap (i.comp iK) ≫ z.x := hw.1.trans hy'
  exact integral_of_eq T' (i.comp io) w hwx M'.m1 M'.m2 hLw
    (secInt_baseChange T T' ψ i hψ M.m1 M.m2 M'.m1 M'.m2 n n' hx h1 h2 hy hwx _ _ hs2 hS)

theorem evR_chg {K S : Type} [Field K] [Algebra c.F K] [Field S] [Algebra c.F S] {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {y₀ : FrPt Xo c K} {G : MvPolynomial (FrVar Dw.mult) K}
    (hG : IsFrPoly F y₀ G) (φ : K →ₐ[c.F] S) {y y' w : FrPt Xo c S} (hy : FrMap φ y₀ y)
    {g X Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S} {s : S} (hs : s ≠ 0)
    (hY : ∀ b, IsUnit (Y b).det) (hXY : ∀ b, (Y b).transpose = X b * g b)
    (h : FrChg g s y y') (hw : FrChg X 1 y' w) :
    evR Xo c F w = s ^ n * evalFr (MvPolynomial.map φ.toRingHom G) Y := by
  have hYt : ∀ b, IsUnit ((Y b).transpose).det := fun b => by rw [Matrix.det_transpose]; exact hY b
  obtain ⟨w₀, hw₀, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y (fun b => (Y b).transpose) 1 hYt
  obtain ⟨w₁, hw₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S w₀ (fun _ => 1) (Units.mk0 s hs)
    (fun _ => by simp)
  have c1 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y w₀ w₁).2 _ _ _ _ hw₀ hw₁
  have c2 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y y' w).2 _ _ _ _ h hw
  have e : w₁ = w := by
    refine (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y (fun b => (Y b).transpose) (Units.mk0 s hs) hYt).unique
      ?_ ?_
    · simpa using c1
    · simpa [hXY] using c2
  rw [← e, evR_scale hF _ hw₁, hG S φ y w₀ Y hY hy hw₀]
  rfl

theorem step5Loc_cmPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ G : MvPolynomial (FrVar Dw.mult) z.K, IsFrPoly F z.y G → ∀ p, Step5Loc z.e z.Tl.dual z.LamL z.ℓ z.U G n p := by
  intro E _ _ _ H Dw l Xo c _ z f La hz a n F hF hv G hG p
  obtain ⟨ca, hca⟩ := exists_isLocGen p z.Tl.I
  obtain ⟨cd, hcd⟩ := exists_isLocGen p z.LamL.I
  choose cl hcl using fun j => exists_isLocGen p (z.ℓ j).I
  refine ⟨ca⁻¹, cd, cl, isLocGen_inv hca, hcd, hcl,
    GlobalTheory.LamF.letters_det_valuation_le E H l c _ _ f z.obj La hz.1 z.letters hz.2.1 p cd cl hcd hcl, ?_⟩
  obtain ⟨T, iK, hT, hiK⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff z.K p
  obtain ⟨M⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  obtain ⟨u, hu⟩ := GlobalTheory.T.integralGenerator_associated_localGenerator_CM_line E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hS ca hca
  refine ⟨T.V, T.Fr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, iK,
    fun b => (g b)⁻¹, inferInstance, hT, hiK, fun b => (Matrix.isUnit_nonsing_inv_det _ (hg b)).ne_zero,
    fun b j k => GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j k _ (hcl _), ?_⟩
  intro W KW _ _ _ _ _ _ _ fW hW hWf _ hfW Y X hX hXY
  have hinj : Function.Injective (algebraMap T.V W) := by
    intro x y h
    apply IsFractionRing.injective T.V T.Fr
    apply fW.injective
    rw [hfW, hfW, h]
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  let T' : CDVR := ⟨W⟩
  let κ : KW →+* T'.Fr := ((FractionRing.algEquiv W KW).symm : KW ≃ₐ[W] FractionRing W).toRingEquiv.toRingHom
  have hκ : ∀ w : W, κ (algebraMap W KW w) = algebraMap T'.V T'.Fr w := fun w =>
    (FractionRing.algEquiv W KW).symm.commutes w
  let i : T.Fr →+* T'.Fr := κ.comp fW
  have hψ : (algebraMap T'.V T'.Fr).comp (algebraMap T.V W) = i.comp (algebraMap T.V T.Fr) := by
    ext x
    show _ = κ (fW _)
    rw [hfW, hκ]
    rfl
  letI := (i.comp io).toAlgebra
  let iA : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨yW, hyW⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA yT
  obtain ⟨y'', hy''⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA y'
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c _ _ iA yT y' yW y'' g s hy' hyW).1 hy''
  have hXt : ∀ b, IsUnit ((X b).transpose : Matrix _ _ T'.V).det := fun b => by
    rw [Matrix.det_transpose]; exact hX b
  have hXu : ∀ b, IsUnit (((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr)).det := fun b => by
    have := (hXt b).map (algebraMap T'.V T'.Fr)
    rwa [RingHom.map_det] at this
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T'.Fr y'' _ 1 hXu
  have hint := integral_baseChange_chg z T T' iK M (algebraMap T.V W) i hψ io iA y' y'' w
    (fun b => (X b).transpose) rfl (hy'.1.trans hyx) hL hS hy'' hXt hw
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg E H Dw l Xo c F hv T' (i.comp io) hWf w hint
  have hYX : ∀ b, (Y b).transpose = ((X b).map (algebraMap W KW)).transpose * (g b).map fW := fun b => by
    rw [← hXY b, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.map_mul,
      Matrix.nonsing_inv_mul _ (hg b)]
    simp
  have hYX' : ∀ b, ((Y b).map κ).transpose =
      ((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr) * (g b).map iA := fun b => by
    rw [← Matrix.transpose_map, hYX b, Matrix.map_mul]
    congr 1
    ext j k
    exact hκ _
  have hYu : ∀ b, IsUnit ((Y b).map κ).det := fun b => by
    rw [← Matrix.det_transpose, hYX' b, Matrix.det_mul]
    refine (hXu b).mul ?_
    have := (hg b).map i
    rwa [RingHom.map_det] at this
  have hval := evR_chg hF hG (iA.comp φ) (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ iA hyT hyW)
    ((map_ne_zero iA).2 s.ne_zero) hYu hYX' hc hw
  refine ⟨algebraMap T.V W ↑u⁻¹ ^ n * w₀, κ.injective ?_⟩
  have hP : MvPolynomial.map κ (MvPolynomial.map fW (MvPolynomial.map iK G)) =
      MvPolynomial.map (iA.comp φ).toRingHom G := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    rfl
  have hsn : (iA s : T'.Fr) ≠ 0 := (map_ne_zero iA).2 s.ne_zero
  have hu' : κ (fW (iK ca⁻¹)) * κ (algebraMap W KW (algebraMap T.V W ↑u⁻¹)) * iA s = 1 := by
    rw [← hfW]
    show i _ * i _ * i _ = 1
    rw [← map_mul, ← map_mul, hu, map_inv₀, _root_.mul_mul_mul_comm, inv_mul_cancel₀ ((map_ne_zero iK).2 hca.1),
      ← map_mul, Units.inv_mul, map_one, _root_.one_mul, map_one]
  rw [map_evalFr, hP]
  simp only [map_mul, map_pow]
  rw [hκ w₀, hw₀, hval, ← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow, hu', one_pow, _root_.one_mul]

end GlobalTheory.LamT.LocClause
end
end
