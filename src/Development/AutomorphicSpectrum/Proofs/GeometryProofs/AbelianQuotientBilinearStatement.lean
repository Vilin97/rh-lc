module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalBilinearTermProductStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientDifferentialMatrixStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeRelation
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeTransformStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeUnitStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermDimensionUniqueStatement
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqB
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
import Mathlib.RingTheory.Henselian
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLineBundleGauge
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubstitutionBilinearFormTransformStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitTrivialOnBothAxesStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeRelationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_gauge_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ lam : PS k 2 d, (∀ m, ∃ U : (Jet k (Fin 2 × Fin d) m)ˣ, (U : Jet k (Fin 2 × Fin d) m) = psJet m lam ∧ Tr w (cubeF t x ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (fun I => (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)] I) (cε 2) (g.e m) (LB.pullGen Q.tB.PP.L (cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)]) (cε 2) (gB.e m) (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) (unitΓ U⁻¹)) → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → AdRel Q.tB (𝟙 (Sp k)) d' gB.x gB.B.A.act gB.B.ad gB.e a wB → Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) 1 → subQ Qs (gB.B.ad a) * ev (n := 2) ![pt k d 0, comp1 (g.B.A.act (H.bar a)) (pt k d 1)] lam = ev (n := 2) ![comp1 (g.B.A.act a) (pt k d 0), pt k d 1] lam * g.B.ad a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGermPowerSeries

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap

open Formalism.MainNotions.ModuliIntegralCharts.H1

section Jets

variable {k : Type} [CommRing k]

theorem exists_jetMap {κ κ' : Type} {m : ℕ} (χ : Jet k κ m →ₐ[k] Jet k κ' m)
    (h : ∀ q, (jetAug : Jet k κ' m →ₐ[k] k) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) :
    ∃ (φ : κ → MvPolynomial κ' k) (hφ : ∀ i, φ i ∈ orig k κ'), χ = jetMap φ hφ := by
  choose P hP using fun q => Ideal.Quotient.mk_surjective (χ (Ideal.Quotient.mk (orig k κ ^ (m + 1)) (MvPolynomial.X q)))
  have hc : ∀ q, MvPolynomial.constantCoeff (P q) = 0 := fun q => by
    have e : (jetAug : Jet k κ' m →ₐ[k] k) (Ideal.Quotient.mk _ (P q)) = 0 := by rw [hP]; exact h q
    have e' : (MvPolynomial.aeval (fun _ : κ' => (0 : k))) (P q) = 0 := e
    rwa [MvPolynomial.aeval_zero'] at e'
  have hm : ∀ q, P q ∈ orig k κ' := fun q => by
    have := sub_const_mem_orig (P q)
    rwa [hc q, map_zero, sub_zero] at this
  refine ⟨P, hm, GermD.jet_hom_ext fun q => ?_⟩
  rw [GermD.jetMap_mk, MvPolynomial.aeval_X, hP]

end Jets

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

theorem fibPt_fst {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.fst t.G.hom x = y.left :=
  pullback.lift_fst _ _ _

theorem fibPt_snd {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.snd t.G.hom x = spMap (algebraMap k A) :=
  (pullback.lift_snd _ _ _).trans (by simp)

theorem homAt_fibPt {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (y : overAt x A ⟶ t.G) : homAt (𝟙 (Sp k)) f ≫ fibPt t x y = fibPt t x (homAt x f ≫ y) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc]
    erw [fibPt_fst, fibPt_fst]
    rfl
  · rw [Over.comp_left, Category.assoc]
    erw [fibPt_snd, fibPt_snd]
    exact spMap_comp_alg f

theorem one_left_fst {T : Over (Sp k)} :
    (1 : T ⟶ GF t x).left ≫ pullback.fst t.G.hom x = T.hom ≫ x ≫ η[t.G].left := by
  rw [Hom.one_def, Over.comp_left, Category.assoc]
  have e : η[(Over.pullback x).obj t.G].left ≫ pullback.fst t.G.hom x = x ≫ η[t.G].left := by
    rw [Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
      ← pullback.condition_assoc]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  erw [e]
  rfl

theorem fibPt_one {A : Type} [CommRing A] [Algebra k A] : fibPt t x (1 : overAt x A ⟶ t.G) = 1 := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · erw [fibPt_fst, one_left_fst]
    rw [Hom.one_def, Over.comp_left]
    simp
  · erw [fibPt_snd]
    have := Over.w (1 : overAt (𝟙 (Sp k)) A ⟶ GF t x)
    simpa using this.symm

end Fibre

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {k : Type} [Field k] {x : Sp k ⟶ X}

theorem q_one (Q : AbQuot t x) {T : Over (Sp k)} : (1 : T ⟶ GF t x) ≫ Q.q = 1 := by
  have := Q.q_hom
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]

theorem chart_trunc {S : Type} [CommRing S] {Y : Scheme.{0}} {G : Over Y} (x₀ : Sp S ⟶ Y) {d e : ℕ}
    (gx : ∀ m, jOG x₀ e m 1 ⟶ G)
    (htr : ∀ m, homAt x₀ (jetTrunc : Jet S (Fin 1 × Fin e) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin e) m) ≫ gx (m + 1) = gx m)
    (y : ∀ m, overAt x₀ (Jet S (Fin 1 × Fin d) m) ⟶ G)
    (hy : ∀ m, homAt x₀ (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ y (m + 1) = y m)
    (χ : ∀ m, Jet S (Fin 1 × Fin e) m →ₐ[S] Jet S (Fin 1 × Fin d) m)
    (hz : ∀ m q, (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (χ m (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0)
    (hχ : ∀ m, y m = homAt x₀ (χ m) ≫ gx m)
    (hu : ∀ m (ψ : Jet S (Fin 1 × Fin e) m →ₐ[S] Jet S (Fin 1 × Fin d) m),
      (∀ q, (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (ψ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) →
        y m = homAt x₀ ψ ≫ gx m → ψ = χ m) (m : ℕ) (q : Fin 1 × Fin e) :
    (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m)
      (χ (m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X q))) = χ m (Ideal.Quotient.mk _ (MvPolynomial.X q)) := by
  obtain ⟨φ, hφ, e₁⟩ := exists_jetMap (χ (m + 1)) (hz (m + 1))
  have hcomm : (jetMap (m := m) φ hφ).comp
      (jetTrunc : Jet S (Fin 1 × Fin e) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin e) m) =
      (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m).comp (χ (m + 1)) := by
    rw [e₁]
    exact GermD.jet_hom_ext fun i => rfl
  have hψ : jetMap (m := m) φ hφ = χ m := by
    refine hu m _ (fun q => ?_) ?_
    · have h := hz (m + 1) q
      rw [e₁] at h
      exact h
    · rw [← hy m, hχ (m + 1), ← htr m, ← Category.assoc, ← Category.assoc, GermD.homAt_comp, GermD.homAt_comp, hcomm]
  rw [← hψ]
  exact (AlgHom.congr_fun hcomm _).symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∃ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) ∧ (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) := by
  intro E _ _ _ H _ hst X t k _ _ p _ _ x Q d d' g gB
  have hy₀ : ∀ m, homAt (𝟙 (Sp k)) (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) ≫ (fibPt t x (g.x m) ≫ Q.q) = 1 := fun m => by
    rw [← Category.assoc, homAt_fibPt, g.chart.zero m, fibPt_one, q_one]
  have hy₁ : ∀ m, homAt (𝟙 (Sp k)) (jetTrunc : Jet k (Fin 1 × Fin d) (m + 1) →ₐ[k] Jet k (Fin 1 × Fin d) m) ≫
      (fibPt t x (g.x (m + 1)) ≫ Q.q) = fibPt t x (g.x m) ≫ Q.q := fun m => by
    rw [← Category.assoc, homAt_fibPt, g.chart.trunc m]
  choose χ hχ hu using fun m =>
    (GlobalTheory.T.formal_germ_dimension_unique E H hst (Sp k) Q.tB k (𝟙 (Sp k)) d' gB).2 (Fin 1 × Fin d) m _ (hy₀ m)
  have hc := chart_trunc (𝟙 (Sp k)) gB.x gB.chart.trunc (fun m => fibPt t x (g.x m) ≫ Q.q) hy₁ χ
    (fun m => (hχ m).1) (fun m => (hχ m).2) (fun m ψ h₁ h₂ => hu m ψ ⟨h₁, h₂⟩)
  choose Qs hQs using fun i : Fin d' => GaugeR.exists_ps_of_compat
    (fun m => χ m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))) (fun m => hc m _)
  have hconst : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0 := fun i => by
    rw [← GaugeR.jetAug_psJet 0 (Qs i), hQs i 0]
    exact (hχ 0).1 _
  refine ⟨Qs, hconst, fun m => ?_⟩
  have he : sub1 Qs m = χ m := by
    refine GermD.jet_hom_ext fun q => ?_
    obtain ⟨a, i⟩ := q
    obtain rfl : a = 0 := Subsingleton.elim _ _
    have h0 : MvPolynomial.constantCoeff (psTrunc m (Qs i)) = 0 := by
      rw [MvPolynomial.constantCoeff_eq, GermFun.coeff_psTrunc _ _ _ (by simp)]
      exact hconst i
    rw [← hQs i m, sub1, jetSubstP, GermD.jetMap_mk, MvPolynomial.aeval_X, h0, map_zero, sub_zero]
    rfl
  rw [he]
  exact (hχ m).2

end Main

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGermPowerSeriesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_germ_power_series : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∃ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) ∧ (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap.main | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap.main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLineBundleGaugeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_line_bundle_gauge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → ∃ u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ, Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr.adjunction_ratio | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr.adjunction_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr.adjunction_ratio <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientBilinear

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

theorem frame_gauge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ P : Matrix (Fin d') (Fin d) k, Q.IsDiff g gB P → ∃ Z : Matrix (Fin d) (Fin d) k, ∀ a, bil (g.B.ad a) 1 1 + (rho g.B a).transpose * Z - Z * rho g.B (star a) = P.transpose * bil (gB.B.ad a) 1 1 * P := by
  intro E _ _ _ H _ hstar X t k _ _ p _ _ x Q d d' g gB P hP
  obtain ⟨w, hw⟩ := Q.bun
  obtain ⟨Qs, hc, hQ⟩ := GlobalTheory.T.abelian_quotient_germ_power_series E H hstar X t k p x Q d d' g gB
  have hl := GlobalTheory.T.abelian_quotient_differential_matrix E H hstar X t k p x Q d d' g gB P hP Qs hc hQ
  obtain ⟨lam, hax, hlam⟩ := GlobalTheory.T.abelian_quotient_gauge_transform E H hstar X t k p x Q d d' g gB w hw Qs hc hQ
  refine ⟨bil lam 1 1, fun a => ?_⟩
  obtain ⟨wL, hwL, hrL⟩ := g.frame.ad a
  obtain ⟨wB, hwB, hrB⟩ := gB.frame.ad a
  obtain ⟨u, hu⟩ := GlobalTheory.T.abelian_quotient_line_bundle_gauge E H hstar X t k p x Q d d' g gB w hw a wL wB hwL hwB
  obtain ⟨h0, h1⟩ := GlobalTheory.T.abelian_quotient_gauge_unit E H hstar X t k p x Q d d' g gB w hw Qs hc hQ a wL wB hwL hwB hrL hrB u hu
  obtain rfl := GlobalTheory.T.unit_trivial_on_both_axes E H hstar X t k p x Q d g u h0 h1
  have hrel := GlobalTheory.T.abelian_quotient_gauge_relation E H hstar X t k p x Q d d' g gB w hw Qs hc hQ lam hlam a wL wB hwL hwB hrL hrB hu
  rw [← hstar a] at hrel
  obtain ⟨hA, hbA⟩ := GlobalTheory.T.substitution_bilinear_form_transform k d d' Qs (gB.B.ad a) hc ⟨gB.B.adjoint_zero_fst a, gB.B.adjoint_zero_snd a⟩
  have hadx : AxOne (g.B.ad a) := ⟨g.B.adjoint_zero_fst a, g.B.adjoint_zero_snd a⟩
  have hcs : ∀ (b : 𝓞 E) (i : Fin d), MvPowerSeries.constantCoeff (g.B.A.act b i) = 0 := fun b i => g.B.A.const b i
  have hp0 : ∀ i : Fin d, MvPowerSeries.constantCoeff (pt k (n := 1) d 0 i) = 0 := fun i => by simp [pt]
  have hp2 : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff (pt k (n := 2) d j i) = 0 := fun j i => by simp [pt]
  obtain ⟨-, -, -, hT, hbT, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d lam lam (pt k d 0) (g.B.A.act (star a)) hax hax hp0 (hcs _)
  obtain ⟨-, -, -, hS, hbS, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d lam lam (g.B.A.act a) (pt k d 0) hax hax (hcs _) hp0
  rw [germ_comp1_zero_point_left _ (hp2 0)] at hT hbT
  rw [germ_comp1_zero_point_left _ (hp2 1)] at hS hbS
  obtain ⟨-, -, e1, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d (subQ Qs (gB.B.ad a)) _ (pt k d 0) (pt k d 0) hA hT hp0 hp0
  obtain ⟨-, -, e2, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d _ (g.B.ad a) (pt k d 0) (pt k d 0) hS hadx hp0 hp0
  have h := congrArg (fun f => bil f 1 1) hrel
  beta_reduce at h
  rw [e1, e2, hbT, hbS, hbA, hl, lin_pt_eq_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h
  change _ + (rho g.B a).transpose * _ - _ * rho g.B (star a) = _
  change _ + bil lam 1 1 * rho g.B (star a) = (rho g.B a).transpose * bil lam 1 1 + _ at h
  rw [eq_sub_of_add_eq h]
  abel

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientBilinearStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_bilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ P : Matrix (Fin d') (Fin d) k, Q.IsDiff g gB P → ∃ Z : Matrix (Fin d) (Fin d) k, ∀ a, bil (g.B.ad a) 1 1 + (rho g.B a).transpose * Z - Z * rho g.B (star a) = P.transpose * bil (gB.B.ad a) 1 1 * P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.frame_gauge | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.frame_gauge | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.frame_gauge <;> assumption)
end
end
