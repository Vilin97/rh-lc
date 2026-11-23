module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FlatSat
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfFamily
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupCLeISupGeneric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedUniformisationComponentsPeriodSpacesBiject
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfD
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGagaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterPeriodFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieSignatureNumberField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoDatumExistsStatement
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsCoordLattice
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemSpan
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FinrankOfLieMult
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HeightComparisonGlobalModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Rt0ConjNegNeZero
public import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfB
import Mathlib.Algebra.AffineMonoid.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyUniformisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.exists_family_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Comp Xo c) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), 1 ≤ r → IsUnf U → (∀ b : Om Z, IsAlgebraic c.F b → b ∈ (algebraMap c.F (Om Z)).range) → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → (Set.range y ⊆ (Z : Set (Xo.XF c)) ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) := by
  intro E _ _ _ H D l Xo c Z r U h1 hU hac
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨-, -, hcov, -, -, g, e, F, ik, φ, hEF, hP⟩ := id hU
  have hty : IsTypeFn H D.p D.q (fun j => relab c c.F.val.toRingHom (e j).1) :=
    (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 D g e
  have hinj := (GlobalTheory.CompBij.ik_bijective E H D l Xo c _ r U h1 hσ hU g e F ik φ hEF
    fun k x => (hP k x).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩).1
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c
  choose q hq using GlobalTheory.UnifComp.exists_liesOn (Formalism.L2.PjFree.Unf.ofPj U) hU
  obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model (Formalism.L2.PjFree.Unf.ofPj U) hU hG Z
  have hqk : q k = Z := GlobalTheory.UnifComp.eq_of_carries hk (hq k)
  have comp_eq_of_algClosedAt {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (h : GenFrEx Xo c)
      (Z : Comp Xo c) (hac : ∀ a : Om Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om Z)).range)
      (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom)
      (hk : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y')
      (hk' : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k' x') y') : k = k' := by
    obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c
    obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
    obtain ⟨C, ψ, z, t, hz, ht⟩ := hA h (Om Z) (genFr h Z)
    let : Algebra c.F C.R := C.R.algebra
    have hCZ : C.Z = Z := by
      by_contra hne
      let s₀ : Sp (Om Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om Z))
      refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c C.Z Z hne) ?_ (GlobalTheory.AllWt.liesOn_genFr h Z s₀)
      rw [GlobalTheory.UnifComp.ptF_frBor ht, GlobalTheory.UnifComp.ptF_frMap hz, Scheme.Hom.comp_apply]
      let η : Sp C.R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.R)
      let sC : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
      have he : spMap C.R.val.toRingHom sC = η :=
        PrimeSpectrum.ext (Ideal.comap_bot_of_injective C.R.val.toRingHom Subtype.val_injective)
      have hη : GlobalTheory.AllWt.ptF C.y η ∈ (C.Z : Set (Xo.XF c)) := by
        have hgen := GlobalTheory.AllWt.liesOn_genFr h C.Z sC
        rw [← GlobalTheory.UnifComp.ptF_frBor C.bor, GlobalTheory.UnifComp.ptF_frMap C.gen,
          Scheme.Hom.comp_apply, he] at hgen
        exact hgen
      have hspec : η ⤳ spMap ψ.toRingHom s₀ :=
        (PrimeSpectrum.le_iff_specializes (R := C.R) _ _).1 bot_le
      exact (hspec.map (GlobalTheory.AllWt.ptF C.y).continuous).mem_closed
        (isClosed_of_mem_irreducibleComponents _ C.Z.2) hη
    have : Algebra.Smooth c.F C.R := C.sm
    have hread : ∀ (k : U.Comp) (x : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ))
        (t : Ix D → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') →
        ∃ f : C.R → ℂ, GlobalTheory.GeomConn.ReadOn (Formalism.L2.PjFree.Unf.ofPj U) C.y f k := by
      rintro k x ⟨φ, y', t', hy', ht'⟩
      obtain ⟨w, hw⟩ := hL.bc _ _ φ z
      exact ⟨_, φ.comp ψ, w, x, _, fun _ => rfl, PullbackSections.frMap_trans _ _ hz hw,
        hmul _ _ _ _ _ ht' (hinv _ _ _ (GlobalTheory.SupGeneric.frBor_of_frMap φ ht hw hy'))⟩
    obtain ⟨f, hf⟩ := hread k x hk
    obtain ⟨f', hf'⟩ := hread k' x' hk'
    refine GlobalTheory.GeomConn.ReadOn.eq_of_isPreconnected (U := Formalism.L2.PjFree.Unf.ofPj U) hσ hU ?_ hf hf'
    have hac' : ∀ a : Om C.Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om C.Z)).range := by
      rw [hCZ]; exact hac
    exact GlobalTheory.GeomConn.isPreconnected_points_over C.R.val Subtype.val_injective hac' σ
  have huniq : ∀ k', q k' = Z → k' = k := by
    intro k' hk'
    obtain ⟨Z', hZ'⟩ := GlobalTheory.CompModel.exists_comp (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hG k'
    obtain rfl : Z' = Z := (GlobalTheory.UnifComp.eq_of_carries hZ' (hq k')).symm.trans hk'
    obtain ⟨P, w, x, t, hw, ht⟩ := hk
    obtain ⟨P', w', x', t', hw', ht'⟩ := hZ'
    exact comp_eq_of_algClosedAt U hσ hU hG Z' hac k' k x' x
      ⟨P', w', t', hw', ht'⟩ ⟨P, w, t, hw, ht⟩
  have hfr : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      ∃ (k' : U.Comp) (x : (U.X k').dom) (t : Ix D → (CAt c.F.val.toRingHom)ˣ)
        (z : FrPt Xo c (CAt c.F.val.toRingHom)),
        FrBor t (U.un k' x) z ∧ z.x = under y ∧ GlobalTheory.AllWt.ptF z = y := by
    intro y hy
    have hover : under y ≫ Xo.s = sOf c ℂ := by
      show (y ≫ pullback.fst _ _) ≫ Xo.s = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy, sOf, ← Spec.map_comp]
      rfl
    obtain ⟨z, hz⟩ := Formalism.L2.Pj.exists_frPt_local (Xo := Xo) (c := c) (L := ℂ)
      GlobalTheory.firstFiveLaws.2.1.secTwist (under y) hover
    obtain ⟨k', x, t, hb⟩ := hcov z
    refine ⟨k', x, t, z, hb, hz, ?_⟩
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hz
    · exact (pullback.lift_snd _ _ _).trans hy.symm
  refine ⟨g, _, F, ik k, hty, fun y hy => ⟨fun hZ => ?_, fun ⟨P, hP', hPy⟩ => ?_⟩⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    have hk' : q k' = Z := by
      by_contra hne
      let s₀ : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) ?_ (hZ ⟨s₀, rfl⟩)
      have := hq k' x s₀
      change GlobalTheory.AllWt.ptF (U.un k' x) s₀ ∈ _ at this
      rwa [← GlobalTheory.UnifComp.ptF_frBor hb, hzy] at this
    obtain rfl := huniq k' hk'
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    exact ⟨Pm, hPm, hzx.symm.trans (hb.1.trans hx)⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    have e1 : ik k' = ik k := F.disj _ _ Pm P hPm hP' (hx.symm.trans (hb.1.symm.trans (hzx.trans hPy)))
    obtain rfl := hinj e1
    rintro _ ⟨s, rfl⟩
    rw [← hqk, ← hzy, GlobalTheory.UnifComp.ptF_frBor hb]
    exact hq k' x s
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.LogOmBound

section

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar

namespace LevelTowerAlt

theorem logOm_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ∃ (_ : NeZero H.d) (χ : DirichletCharacter ℂ H.d),
      GlobalTheory.IsKroneckerChar χ ∧ |(GlobalTheory.CM.logOm E χ).re| ≤ C * (1 + Real.log (hostRd E) + |hostLval H|) := by
  have hγ : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  refine ⟨1 + Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|, by positivity, ?_⟩
  intro E _ _ _ H
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  refine ⟨⟨H.d_prime.ne_zero⟩, (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ),
    GlobalTheory.isKroneckerChar_quadraticChar (by have := H.d_mod; omega), ?_⟩
  have hL : (GlobalTheory.CM.logOm E ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ))).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) - hostLval H := by
    simp only [GlobalTheory.CM.logOm, Complex.sub_re, Complex.ofReal_re]
    rfl
  have hrd : rootDiscr E = hostRd E := by
    unfold hostRd
    rw [NumberField.rootDiscr_def, Int.cast_abs, one_div]
  have h1 : 1 ≤ hostRd E := by
    unfold hostRd
    apply Real.one_le_rpow
    · have := Int.one_le_abs (NumberField.discr_ne_zero E)
      rw [← Int.cast_abs]
      exact_mod_cast this
    · positivity
  have hb0 : 0 ≤ Real.log (hostRd E) := Real.log_nonneg h1
  have hlogdiv : Real.log (2 * Real.pi / rootDiscr E) = Real.log (2 * Real.pi) - Real.log (hostRd E) := by
    rw [hrd, Real.log_div (by positivity) (by linarith)]
  rw [hL, hlogdiv]
  have ha1 := le_abs_self (Real.log (2 * Real.pi))
  have ha2 := neg_abs_le (Real.log (2 * Real.pi))
  have hl1 := le_abs_self (hostLval H)
  have hl2 := neg_abs_le (hostLval H)
  have hb : |Real.eulerMascheroniConstant + (Real.log (2 * Real.pi) - Real.log (hostRd E)) - hostLval H| ≤
      Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)| + Real.log (hostRd E) + |hostLval H| :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have hm : 0 ≤ (Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|) *
      (Real.log (hostRd E) + |hostLval H|) := by positivity
  nlinarith

end LevelTowerAlt
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PhiDegFibLatLeOfIsOFamilyOfIsAdapted

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
namespace GlobalTheory.CompanionTheory.Ar.Cusp.U4

open LevelTowerAlt GlobalTheory.CompanionTheory.Ar.Fl GroundTheory.Heights₂.Heights

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem flat_point_of_principal_sign (hG : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given) (hF : FlatDegree) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : Host E) {L : Type} [Field L] [NumberField L] (t : SAB H (Sp L)) (ht : IsPrincipal t) (ρ : L) (p' q' : ℕ)
    (σ : L →+* ℂ) (hσ : σ ρ = H.rt0)
    (hs : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult t.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ q'))
    (h1 : 1 ≤ p' + q') (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) [NeZero H.d] (χ : DirichletCharacter ℂ H.d)
    (hχ : GlobalTheory.IsKroneckerChar χ) :
    ∃ (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : NumberField c.F) (F : Type) (_ : Field F)
      (_ : NumberField F) (β : c.F →+* F) (e : L →+* F) (io : F →+* ℂ) (tK : SAB H (Sp F)) (_ : SABMap tK t (spMap e))
      (y : Sp F ⟶ Xo.XF c) (_ : SABMap tK Xo.univ.t (under y)) (U : Set (Xo.XF c)) (φ : FrameFn Xo c)
      (N : LogNorms c.F), D.p = p' ∧ D.q = q' ∧ (∀ x, io (β x) = (x : ℂ)) ∧ (∀ x, io (e x) = σ x) ∧
      y ≫ pullback.snd _ _ = spMap β ∧ Set.range y ⊆ U ∧ IsLineFn U τ φ ∧ (∀ s, HasInfNorm U τ φ s (N.inf s)) ∧
      (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) ∧ N.IsAdelic ∧
      N.deg = ((p' : ℝ) - q') / 2 * (GlobalTheory.CM.logOm E χ).re := by
  obtain ⟨⟨hP, hN, -, -⟩, -, -, -, hResK, -, -, hGaga, -⟩ := hG
  obtain ⟨D, rfl, rfl, ⟨I⟩⟩ := GlobalTheory.T.tate_iso_datum_exists E H L t ht σ p' q' fun τ => by
    have := hs ℂ σ τ
    rwa [hσ] at this
  let Xo : ∀ l : Level H, Moduli D l := fun l => (hN E H D l h1).some
  obtain ⟨l, hA, hg⟩ := GlobalTheory.GlobalModelGuards.exists_good_level H
  obtain ⟨c₀⟩ := GlobalTheory.ModuliProbe.coeff_nonempty l
  obtain ⟨-, c, -, hc⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H D l (Xo l) c₀ h1
  haveI := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨F, hfin, hF', e, o, he, ⟨m⟩⟩ := SabModel.exists_obj_ext E H D l L t ht hA ρ σ hσ hs I c.F c.fin c.le
  haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := (Xo l).rep (Sp F) _ inferInstance o
  let bF : c.F →+* F := (IntermediateField.inclusion hF').toRingHom
  let y : Sp F ⟶ (Xo l).XF c := pullback.lift f (spMap bF) (by
    rw [hf, ← Spec.map_comp]
    rfl)
  have hy1 : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hy2 : y ≫ pullback.snd _ _ = spMap bF := pullback.lift_snd _ _ _
  let x₀ : (Xo l).XF c := y (IsLocalRing.closedPoint F)
  let Z : Formalism.L2.Pj.Comp (Xo l) c := ⟨irreducibleComponent x₀, irreducibleComponent_mem_irreducibleComponents x₀⟩
  have hyZ : Set.range y ⊆ (Z : Set ((Xo l).XF c)) := by
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s (IsLocalRing.closedPoint F)]
    exact mem_irreducibleComponent
  obtain ⟨V, hV, -⟩ := GlobalTheory.UnifFamily.exists_unf_family E H D l (Xo l) c h1
  obtain ⟨g, ty, FU, i, hty, hper⟩ := GlobalTheory.T.exists_family_uniformisation E H D l (Xo l) c Z (D.p + D.q) (V c.F.val.toRingHom).toPj h1
    (hV c.F.val.toRingHom (show Formalism.L2.Pj.GoodEmb c c.F.val.toRingHom from rfl)).1 (hc c le_rfl Z)
  have hclo : IsClopen (Z : Set ((Xo l).XF c)) :=
    Formalism.L2.Pj.CompSplitPfB.cspB_isClopen (Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj (Xo l) c) Z
  obtain ⟨φ, N, hfg, hn, -⟩ := GlobalTheory.T.flat_theorem_of_resolution_gaga hResK hGaga hP E H D Xo l c (Z : Set ((Xo l).XF c)) τ g ty FU i h1 hτ hg
    hty hclo Z.2.1 hper
  let N' : LogNorms c.F := ⟨N.inf, fun p κ => N.fin p κ +
    D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖)⟩
  obtain ⟨had, hdeg⟩ := GlobalTheory.T.kronecker_character_period_formula hF E H D l (Xo l) c g ty FU i _ τ φ N' χ hχ hty hτ hfg hn.1 hn.2
  exact ⟨D, l, Xo l, c, inferInstance, F, inferInstance, inferInstance, bF, e, F.val.toRingHom, o.t, m, y,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast mf.toSABMap hy1.symm, Z, φ, N', rfl, rfl, fun _ => rfl, he, hy2, hyZ, hfg.line, hn.1,
    hn.2, had, hdeg⟩

theorem flat_hermitian_fibre_signature (hG : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given) (hF : FlatDegree) (H : Host E) {L : Type} [Field L] [NumberField L]
    {t' : SAB H (Sp (𝓞 L))} {tB : SAB H (Sp L)} (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L)))
    {B : HermitianBundle.{0} L} (MB : LieModel t'.G (𝟙 _) B.carrier) {ρM : 𝓞 E →+* Module.End (𝓞 L) B.carrier}
    (s₁ s₂ : 𝓞 E →+* 𝓞 L) (hP : IsPrincipal tB) (hfib : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB)
    (hρ : MB.IsActOf t'.act.act ρM) (ρ : L) (p' q' : ℕ) (σ : L →+* ℂ) (hσ : σ ρ = H.rt0)
    (hs : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult tB.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult tB.act (spMap g) τ q'))
    (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) (h₁ : ∀ a, σ (s₁ a : L) = τ (a : E))
    (h₂ : ∀ a, σ (s₂ a : L) = starRingEnd ℂ (τ (a : E))) [NeZero H.d] (χ : DirichletCharacter ℂ H.d)
    (hχ : GlobalTheory.IsKroneckerChar χ) :
    |B.normDegree (eigSp ρM s₁) - B.normDegree (eigSp ρM s₂)| ≤
      ((B.rank (eigSp ρM s₁) : ℝ) + B.rank (eigSp ρM s₂)) * |(GlobalTheory.CM.logOm E χ).re| := by
  have r₁ : B.rank (eigSp ρM s₁) = p' := rank_eig MB hρ m' σ s₁ ((hs ℂ σ _).1 ((h₁ _).trans (hτ.trans hσ.symm)))
  have r₂ : B.rank (eigSp ρM s₂) = q' := rank_eig MB hρ m' σ s₂ ((hs ℂ σ _).2 fun h => by
    have h3 := (h₂ H.rt).symm.trans (h.trans hσ)
    rw [hτ, (rt0_conj_neg_ne_zero H).1] at h3
    exact (rt0_conj_neg_ne_zero H).2 (by linear_combination (-1 / 2 : ℂ) * h3))
  rcases Nat.eq_zero_or_pos (p' + q') with h0 | h0
  · have e₁ : eigSp ρM s₁ = ⊥ := Submodule.finrank_eq_zero.1 (r₁.trans (by omega))
    have e₂ : eigSp ρM s₂ = ⊥ := Submodule.finrank_eq_zero.1 (r₂.trans (by omega))
    rw [e₁, e₂, sub_self, abs_zero]
    positivity
  obtain ⟨D, l, Xo, c, _, F, _, _, β, e, io, tK, mo, y, mf, U, φ, N, rfl, rfl, hβ, he, hy, hU, hφ, hinf, hfin, had,
    hdeg⟩ := flat_point_of_principal_sign hG hF H tB hP ρ p' q' σ hσ hs h0 τ hτ χ hχ
  obtain ⟨n₀, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m' mo
  let n : SABMap tK t' (spMap (e.comp (algebraMap (𝓞 L) L))) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast n₀ (LevelTowerAlt.spMap_comp _ _).symm
  have hs₁ : β.comp (tauIn c τ) = (e.comp (algebraMap (𝓞 L) L)).comp s₁ :=
    RingHom.ext fun a => io.injective ((hβ _).trans ((he _).trans (h₁ a)).symm)
  have hs₂ : β.comp (tauIn c (ComplexEmbedding.conjugate τ)) = (e.comp (algebraMap (𝓞 L) L)).comp s₂ :=
    RingHom.ext fun a => io.injective ((hβ _).trans ((he _).trans (h₂ a)).symm)
  obtain ⟨vK, vec, k1, k2, -, k4, k5⟩ := exists_vec MB hρ n mf _
    (e.injective.comp (IsFractionRing.injective (𝓞 L) L)) (𝟙 _) (Category.id_comp _) (under y)
    (Category.id_comp _).symm
  obtain ⟨x₁, hx₁⟩ := exists_smul_mem_span B _ r₁
  obtain ⟨x₂, hx₂⟩ := exists_smul_mem_span B _ r₂
  obtain ⟨N₁, a₁, d₁, i₁, f₁⟩ := exists_logNorms B _ x₁ hx₁.1 hx₁.2.1 r₁
  obtain ⟨N₂, a₂, d₂, i₂, f₂⟩ := exists_logNorms B _ x₂ hx₂.1 hx₂.2.1 r₂
  have hfr : IsFramed U τ β y (fun k => vec (x₁ k)) fun k => vec (x₂ k) :=
    ⟨hy, hU, hs₁ ▸ k4 s₁ _ x₁ hx₁.1 hx₁.2.1 hx₁.2.2, hs₂ ▸ k4 s₂ _ x₂ hx₂.1 hx₂.2.1 hx₂.2.2⟩
  have key := deg_eq_sub β e N N₁ N₂ _ (hφ.ne F β y _ _ hfr) had a₁ a₂
    (fun s => by
      rw [i₁, i₂]
      exact inf_norm MB hρ hfib n mf hy hU hφ hs₁ hs₂ k1 k2 hx₁ hx₂ hfr s (hinf _))
    fun p j => by
      obtain ⟨y₁, u₁, T₁, a1, a2, a3, a4, a5, a6, a7⟩ := f₁ p (j.comp e)
      obtain ⟨y₂, u₂, T₂, b1, b2, b3, b4, b5, b6, b7⟩ := f₂ p (j.comp e)
      rw [a7, b7]
      exact fin_norm MB hρ n mf hy hU hφ hs₁ hs₂ k1 k2 k4 k5 hfr p j a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 (hfin p _)
  rw [← d₁, ← d₂, ← key, hdeg, r₁, r₂, abs_mul]
  refine mul_le_mul_of_nonneg_right (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) <;>
    linarith [(Nat.cast_nonneg D.p : (0 : ℝ) ≤ D.p), (Nat.cast_nonneg D.q : (0 : ℝ) ≤ D.q)]

theorem flat_saturation_of_degree (hG : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given) (hF : FlatDegree) : FlatSat := by
  obtain ⟨C, hC, hlog⟩ := logOm_bound
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ H L _ _ t' tB m' B MB ρM s₁ s₂ hP hfib hρ ⟨ρ, p', q', hρ2, hs⟩ hinj hconj
  obtain ⟨_, χ, hχ, hb⟩ := hlog E H
  obtain ⟨σ, hσ⟩ := SabModel.exists_embedding_rt0 H ρ hρ2
  have hi : Function.Injective ((σ.comp (algebraMap (𝓞 L) L)).comp s₁) :=
    (σ.injective.comp (IsFractionRing.injective (𝓞 L) L)).comp hinj
  let τ : E →+* ℂ := IsFractionRing.lift hi
  have hτ : ∀ a : 𝓞 E, σ (s₁ a : L) = τ (a : E) := fun a => (IsFractionRing.lift_algebraMap hi a).symm
  have hsq : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← hτ, H.sqrt_neg_disc_sq]
    have := congrArg ((σ.comp (algebraMap (𝓞 L) L)).comp s₁) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have h : |B.normDegree (eigSp ρM s₁) - B.normDegree (eigSp ρM s₂)| ≤
      ((B.rank (eigSp ρM s₁) : ℝ) + B.rank (eigSp ρM s₂)) * |(GlobalTheory.CM.logOm E χ).re| := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact flat_hermitian_fibre_signature hG hF H m' MB s₁ s₂ hP hfib hρ ρ p' q' σ hσ hs τ h hτ (fun a => by rw [hconj, hτ]) χ hχ
    · rw [abs_sub_comm, add_comm]
      refine flat_hermitian_fibre_signature hG hF H m' MB s₂ s₁ hP hfib hρ ρ p' q' σ hσ hs ((starRingEnd ℂ).comp τ) ?_
        (fun a => by rw [hconj, hτ]; rfl) (fun a => by rw [hτ]; exact (Complex.conj_conj _).symm) χ hχ
      rw [RingHom.comp_apply, h, map_neg, (rt0_conj_neg_ne_zero H).1, neg_neg]
  refine h.trans ?_
  rw [_root_.mul_comm C, _root_.mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end GlobalTheory.CompanionTheory.Ar.Cusp.U4



theorem _root_.GlobalTheory.CompanionTheory.Relay.phiDeg_fibLat_le_of_isOFamily_of_isAdapted : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given → Fl.FlatDegree → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), admitted Xo l c Y Or B₁ → 4 * Dc.f * Dc.N ^ 2 ≤ B → Or.𝔐.IsLinPtOf z P MV A → Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) → r + k = Dc.j' → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q ≤ C * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) :=
  LevelTowerAlt.height_comparison_global_model GlobalTheory.CompanionTheory.Ar.Cusp.U4.flat_saturation_of_degree
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PhiDegFibLatLeOfIsOFamilyOfIsAdaptedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.phiDeg_fibLat_le_of_isOFamily_of_isAdapted : Top.Given → Fl.FlatDegree → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), admitted Xo l c Y Or B₁ → 4 * Dc.f * Dc.N ^ 2 ≤ B → Or.𝔐.IsLinPtOf z P MV A → Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) → r + k = Dc.j' → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q ≤ C * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.phiDeg_fibLat_le_of_isOFamily_of_isAdapted | exact GlobalTheory.CompanionTheory.Relay.phiDeg_fibLat_le_of_isOFamily_of_isAdapted | (intros; apply GlobalTheory.CompanionTheory.Relay.phiDeg_fibLat_le_of_isOFamily_of_isAdapted <;> assumption)
end
end
