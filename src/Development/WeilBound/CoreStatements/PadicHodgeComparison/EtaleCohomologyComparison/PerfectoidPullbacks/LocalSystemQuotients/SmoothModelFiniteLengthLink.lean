module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredModuleFiniteOfGradedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthWittCohomologyStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
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
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherian
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneGradedFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfEtalePoly
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableCoverCechVanishingStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.VanishingOfLadder
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.PolyAll
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.IsProperOfProj
import Mathlib.Tactic.Lemma

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePullBijectiveOfAcyclic

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LengthOneCochainExactness

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

noncomputable def incl (b : IdF A) : CH.Mor (sq b (IdF.bot A)) (CH.modF A) (RingHom.id R) where
  G := 𝟭 C
  τ T := (AlgEquiv.quotientBot R (A.obj T)).toLinearMap ∘ₗ (sqM b (IdF.bot A) T).subtype
  nat φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

theorem incl_mem (b : IdF A) {T : C} (x : (sq b (IdF.bot A)).obj T) : (incl b).τ T x ∈ b.S T := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact hy

theorem cochain_exact (a b : IdF A) (ha : ∀ T, a.S T = ⊤) :
    (∀ n, Function.Injective ((incl b).hom.f n)) ∧
    (∀ n, Function.Exact ((incl b).hom.f n) ((toSq a b ha).hom.f n)) ∧
    ∀ n, Function.Surjective ((toSq a b ha).hom.f n) := by
  refine ⟨fun n x y hxy => ?_, fun n y => ⟨fun hy => ?_, ?_⟩, fun n y => ?_⟩
  · funext s
    have h : (incl b).τ _ (x (s ⋙ 𝟭 C)) = (incl b).τ _ (y (s ⋙ 𝟭 C)) := congrFun hxy s
    exact Subtype.ext ((AlgEquiv.quotientBot R _).injective h)
  · have hm : ∀ s : ComposableArrows C n,
        (show A.obj (s.obj (Fin.last n)) from y s) ∈ b.S (s.obj (Fin.last n)) := fun s => by
      have h := congrArg Subtype.val (congrFun hy s)
      exact Ideal.Quotient.eq_zero_iff_mem.1 h
    exact ⟨fun s => sqMk b (IdF.bot A) _ (hm s), rfl⟩
  · rintro ⟨x, rfl⟩
    funext s
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (incl_mem b (x (s ⋙ 𝟭 C))))
  · have hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)),
        Ideal.Quotient.mk _ t = (show sqM a b _ from y s).1 :=
      fun s => Ideal.Quotient.mk_surjective _
    choose t ht using hm
    exact ⟨t, funext fun s => Subtype.ext (ht s)⟩

theorem pull_toSq_bijective (a b : IdF A) (ha : ∀ T, a.S T = ⊤) :
    (∀ j, Subsingleton (CH.H (sq b (IdF.bot A)) j)) →
      ∀ j, Function.Bijective ((toSq a b ha).pull j) := by
  intro hv j
  obtain ⟨hf, hfg, hg⟩ := cochain_exact a b ha
  obtain ⟨δ, -, -, hex, hex2, -⟩ := CrystallineSemistableComparison.P.les _ _ hf hfg hg
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hex j x).1 hx
    rw [(hv j).elim y 0, map_zero]
  · intro y
    obtain ⟨x, hx⟩ := (hex2 j y).1 ((hv (j + 1)).elim _ _)
    exact ⟨x, hx⟩

end GlobalTheory.CompanionTheory.LengthOneCochainExactness
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePullBijectiveOfAcyclicStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.square_pull_bijective_of_acyclic : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) (ha : ∀ T, a.S T = ⊤),
    (∀ j, Subsingleton (CH.H (sq b (IdF.bot A)) j)) → ∀ j, Function.Bijective ((toSq a b ha).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective | exact GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective | (intros; apply GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherianStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.truncated_witt_isNoetherian : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l], IsNoetherianRing (Wc.Wm l k 1) := by
  first | exact @GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one | exact GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one | (intros; apply GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneGradedFiniteStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.witt_level_one_graded_finite : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (ρ : O →+* k) (U : Cov q) (r j : ℕ),
    Module.Finite (Wc.Wm l k 1) (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) r) (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((r : ℤ) + 1))) j) := by
  first | exact @GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite | exact GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite | (intros; apply GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneVanishAboveDim

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.WittLevel.Van

theorem dividedPowerFiltration_eq_bot {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (hJ : J = ⊥) {r : ℕ} (hr : 1 ≤ r) :
    pdP δ r = ⊥ := by
  subst hJ
  refine Ideal.span_eq_bot.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have h : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra h
    push Not at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by simpa using h)
    omega
  obtain ⟨p, hp, h0⟩ := h
  refine List.prod_eq_zero (List.mem_map.2 ⟨p, hp, ?_⟩)
  have e : p.2 = 0 := hl p hp
  rw [e]
  exact δ.dpow_eval_zero h0

theorem van_on {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (hI : I = ⊥) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {e : ℕ}
    (c : Coord q V e) (d : ℕ) (he : e ≤ d) (j : ℕ) :
    Subsingleton (CH.H (sq (sFil (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V}) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  obtain ⟨c', -, -⟩ := GlobalTheory.CompanionTheory.FlatChartP.exists_flat_chart γ p hp hn q κ c
  have hgood := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hQ : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V} T → InU V T := by
    rintro T ⟨-, W, rfl, h⟩
    exact h
  have hD : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V} c'.D := ⟨trivial, V, rfl, c'.inV⟩
  have hpow : ∀ r, c'.D.pdPow r = (pdP γ r).map c'.D.i := fun r =>
    GlobalTheory.CompanionTheory.ChartFil.dividedPowerFiltration_eq_map γ c'.D.δ c'.D.i c'.D.compat c'.J_eq r
  obtain ⟨PQ, hPQ⟩ := CrystallineSemistableComparison.Pb.Site.poly_all' γ p hp q κ ⊤ (Or.inl rfl) {V}
  refine CrystallineSemistableComparison.Pb.vanishing_of_ladder e PQ (a := sFil _) (b := fun _ => IdF.bot _) (c'.frame hgood _ hQ hD) ((d : ℤ) + 1)
    ⟨fun r' T x hx => ?_, fun r' _ => (hPQ r').1, fun r' _ => (hPQ r').2.1⟩ (fun r' h1 _ x hx => ?_) j
  · have h0 : x = 0 := hx
    rw [h0]
    exact Ideal.zero_mem _
  · have h2 : (show c'.D.B from x) ∈ c'.D.pdPow r'.toNat := hx
    rw [hpow, dividedPowerFiltration_eq_bot γ hI (by omega), Ideal.map_bot] at h2
    exact h2

theorem Im_one_eq_bot (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] : Wc.Im l k 1 = ⊥ := by
  refine (Ideal.map_eq_bot_iff_le_ker _).2 ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  simpa using Ideal.mem_span_singleton_self _

theorem nat_eq_zero (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] :
    ((l : ℕ) : Wc.Wm l k 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  simpa using Ideal.mem_span_singleton_self _

theorem witt_level_one_filtration_vanish : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (d : ℕ), (∀ α, U.d α ≤ d) →
    ∀ j, Subsingleton (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  intro l _ k _ _ _ O _ X q ρ U d hd j
  have hp : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hn : IsNilpotent ((l : ℕ) : Wc.Wm l k 1) := by
    rw [nat_eq_zero]
    exact IsNilpotent.zero
  refine (GlobalTheory.T.stable_cover_cech_vanishing.1 (sq (thFil (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ)) ((d : ℤ) + 1)) (IdF.bot _))
    (⊤ : ObjectProperty (Thick (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ)))) U.U 0).2.1 (fun S hS j => ?_) j
  obtain ⟨α, hα⟩ := id hS
  obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα) (U.inter S hS)
  exact van_on (Wc.pd l k 1) (Im_one_eq_bot l k) l hp hn q _ c' d (hd α) j

end GlobalTheory.CompanionTheory.WittLevel.Van
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneVanishAboveDimStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.witt_level_one_vanish_above_dim : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (d : ℕ), (∀ α, U.d α ≤ d) →
    ∀ j, Subsingleton (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  first | exact @GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | exact GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | (intros; apply GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.SmoothModelFiniteLengthLink

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

private lemma isHecke_div_and_resEtaPow_div {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (d : ℕ)
    (hvan : ∀ j, Subsingleton (CH.H (sq (sFil Q (↑d + 1)) (IdF.bot (sP Q).A)) j))
    (hN : IsNoetherianRing b.R)
    (hgr : ∀ r j : ℕ, Module.Finite b.R (CH.H (sq (sFil Q ↑r) (sFil Q (↑r + 1))) j)) (j : ℕ) :
    Module.Finite b.R (HO Q j) := by
  have hfin := GlobalTheory.T.filtered_module_finite_of_graded (sFil Q) (fun r r' h T => (isFil Q).anti h T) (d + 1) (fun r _ j' => hgr r j') j
  rw [Nat.cast_add, Nat.cast_one] at hfin
  have ha : ∀ T, (sFil Q 0).S T = ⊤ := fun T => (isFil Q).top 0 le_rfl T
  have hb := GlobalTheory.T.square_pull_bijective_of_acyclic (sFil Q 0) (sFil Q (↑d + 1)) ha ?hv j
  · exact Module.Finite.of_surjective (hM := hfin) (LinearEquiv.ofBijective _ hb).symm.toLinearMap
      (LinearEquiv.ofBijective _ hb).symm.surjective
  · exact hvan

theorem wittCohomology_finite_length {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] [Smooth q] (ρ : O →+* k) (j : ℕ) :
    IsFiniteLength (WittVector l k) (CH.H (Wc.OM l (B.schFn q) ρ 1) j) := by
  obtain ⟨U⟩ := (CrystallineSemistableComparison.Pb.cov_ex q).1 inferInstance
  refine GlobalTheory.T.finite_length_witt_cohomology q ρ j ?_
  have hvan := GlobalTheory.T.witt_level_one_vanish_above_dim q ρ U (Finset.univ.sup U.d) (fun α => Finset.le_sup (Finset.mem_univ α))
  have hfin := isHecke_div_and_resEtaPow_div _ _ hvan ?hN ?hgr j
  · refine Module.Finite.of_surjective (hM := hfin)
      (LinearEquiv.ofBijective ((incl ?hle).o.pull j) ?hb).symm.toLinearMap (LinearEquiv.surjective _)
    · intro T hT
      exact ⟨hT.1, ⊤, Set.mem_singleton _, by simp [InU]⟩
    · refine (CrystallineSemistableComparison.Pb.zar ⊤ ?u (Set.range U.U) {⊤} _ ?hcov j).2.2
      · exact Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inl rfl⟩
      · intro W hW
        rw [Set.mem_singleton_iff.mp hW, sSup_range, U.cover]
  · exact GlobalTheory.T.truncated_witt_isNoetherian
  · exact GlobalTheory.T.witt_level_one_graded_finite q ρ U

theorem smooth_model_finite_length_link {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K)
    (hM : M.Sm) (j : ℕ) : IsFiniteLength (WittVector l r.k) ((Wc.HS l (B.schFn M.p) r.ρ j).M 1) := by
  have : IsProper M.p := sm_proper hM
  have : Smooth M.p := hM.2
  exact wittCohomology_finite_length M.p r.ρ j

end CrystallineSemistableComparison.Pb
end
end
end
