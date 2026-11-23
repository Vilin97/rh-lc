module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.Functor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittCoordQuotientPullBijectiveStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBiInf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteQuotientRestrictBijectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelRestrictionBijective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelMorphismCoverCompat

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution GlobalTheory.CompanionTheory.DisoHm

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatCoverGlue



theorem glue {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (n : ℕ) (c : WittVector l k)
    (m : QMor (sW l (B.schFn q) ρ n) (sW l (B.schFn q) ρ (n + 1)) (IdF.span _ c))
    (hG : ∀ (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory),
      stF q ρ n 𝒱 (m.G.obj ⟨T.obj, T.property.1⟩).obj)
    (hloc : ∀ S : Finset U.ι, S.Nonempty → ∀ j, Function.Bijective
      (((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j)) (j : ℕ) :
    Function.Bijective
      (((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j) := by
  have hGU : ∀ (α : U.ι) (T : (stF q ρ (n + 1) (Set.range U.U)).FullSubcategory), InU (U.U α) T.obj →
      InU (U.U α) (m.G.obj ⟨T.obj, T.property.1⟩).obj := fun α T hT => by
    obtain ⟨-, V, rfl, hV⟩ := hG {U.U α} ⟨T.obj, T.property.1, U.U α, rfl, hT⟩
    exact hV
  refine cover_bij ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
      (IdF.span _ c) (fun _ => le_rfl))
    (fun α T => InU (U.U α) T.obj) (fun α T => InU (U.U α) T.obj) (fun α T T' φ hT => Site.inU_hom φ.hom hT)
    (fun α T T' φ hT => Site.inU_hom φ.hom hT) (fun T => ?_) (fun T => ?_) (fun α T hT => hGU α T hT)
    (fun S hS j => ?_) j
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  have h₁ : ∀ (r : ℕ) T, stF q ρ r {⨅ α ∈ S, U.U α} T →
      ∃ hp : stF q ρ r (Set.range U.U) T,
        capS (fun α (T : (stF q ρ r (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S ⟨T, hp⟩ :=
    fun r T hT => ⟨((st_inf _ U S hS T).1 hT).1, ((st_inf _ U S hS T).1 hT).2⟩
  have a₀ := nestAdj (h₁ n) (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  have a₁ := nestAdj (h₁ (n + 1)) (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  let rL : CH.Mor ((capS (fun α (T : (stF q ρ n (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      CH.modF (sV q ρ n (Set.range U.U)).A) (CH.modF (sV q ρ n {⨅ α ∈ S, U.U α}).A) (RingHom.id _) :=
    CH.Mor.restrict _ (nestF (h₁ n))
  let rO : CH.Mor ((capS (fun α (T : (stF q ρ (n + 1) (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      sq (IdF.top (sV q ρ (n + 1) (Set.range U.U)).A) (IdF.span (sV q ρ (n + 1) (Set.range U.U)).A c))
      (sq (IdF.top (sV q ρ (n + 1) {⨅ α ∈ S, U.U α}).A) (IdF.span (sV q ρ (n + 1) {⨅ α ∈ S, U.U α}).A c)) (RingHom.id _) :=
    CH.Mor.restrict _ (nestF (h₁ (n + 1)))
  have bL : Function.Bijective (rL.pull j) := CrystallineSemistableComparison.P.adj _ _ _ a₀ j
  have bO : Function.Bijective (rO.pull j) := CrystallineSemistableComparison.P.adj _ _ _ a₁ j
  refine (Function.Bijective.of_comp_iff' bO _).1 ?_
  have e : ∀ x, rO.pull j ((morU ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => hGU α T (hT α hα)).pull j x) =
      ((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j (rL.pull j x) := by
    intro x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id _) _ rO j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id _) rL _ j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id _) _ _ (𝟙 _) (fun T y => ?_) j x
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  have e2 := funext e
  refine (show Function.Bijective (fun x => rO.pull j ((morU ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => hGU α T (hT α hα)).pull j x)) from ?_)
  rw [e2]
  exact (hloc S hS j).comp bL

end GlobalTheory.CompanionTheory.FlatCoverGlue
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelMorphismCoverCompatStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

theorem _root_.GlobalTheory.T.witt_level_morphism_cover_compat : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (n : ℕ) (c : WittVector l k) (m : QMor (sW l (B.schFn q) ρ n) (sW l (B.schFn q) ρ (n + 1)) (IdF.span _ c)) (hG : ∀ (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory), stF q ρ n 𝒱 (m.G.obj ⟨T.obj, T.property.1⟩).obj), (∀ S : Finset U.ι, S.Nonempty → ∀ j, Function.Bijective (((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o (IdF.span _ c) (fun _ => le_rfl)).pull j)) → ∀ j, Function.Bijective (((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o (IdF.span _ c) (fun _ => le_rfl)).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.FlatCoverGlue.glue | exact GlobalTheory.CompanionTheory.FlatCoverGlue.glue | (intros; apply GlobalTheory.CompanionTheory.FlatCoverGlue.glue <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteRestrictBijective

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatZar

section Main
variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}

def resG (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ)
    (P Q : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (h : Q ≤ P) :
    CH.Mor (P.ι ⋙ Wc.OM l (B.schFn q) ρ m) (Q.ι ⋙ Wc.OM l (B.schFn q) ρ m) (RingHom.id (WittVector l k)) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl


theorem resG_bij (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤)
    (P : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (hP : P = stF q ρ m {⊤}) (h : stF q ρ m 𝒱 ≤ P) (j : ℕ) :
    Function.Bijective ((resG q ρ m P (stF q ρ m 𝒱) h).pull j) := by
  subst hP
  have z := (zar (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT
    (Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inr rfl⟩) 𝒱 {⊤} h
    (fun W _ => by rw [hU]; exact le_top) j).2.2
  have c1 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m {⊤}) j
  have c2 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m 𝒱) j
  refine (Function.Bijective.of_comp_iff' c2 _).1 ?_
  have e : ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m 𝒱)).pull j) ∘ ⇑((resG q ρ m _ (stF q ρ m 𝒱) h).pull j) =
      ⇑((incl h).o.pull j) ∘ ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m {⊤})).pull j) := by
    funext x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  rw [e]
  exact z.comp c1

theorem resV_bij : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resV q ρ m 𝒱).pull j) := by
  intro l _ k _ _ _ O _ X q ρ m 𝒱 hU j
  exact resG_bij q ρ m 𝒱 hU (fl l (B.schFn q) ρ m)
    (GlobalTheory.CompanionTheory.FlatRes.st_top_eq (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT).symm
    (fun _ h => h.1) j

end Main

end GlobalTheory.CompanionTheory.FlatZar

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteRestrictBijectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

theorem _root_.GlobalTheory.T.witt_site_restrict_bijective : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resV q ρ m 𝒱).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.FlatZar.resV_bij | exact GlobalTheory.CompanionTheory.FlatZar.resV_bij | (intros; apply GlobalTheory.CompanionTheory.FlatZar.resV_bij <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.BijOfSub

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb.SubquotientResolution

variable {R : Type} [CommRing R] {D D' : Type 1} [Category.{0} D] [Category.{0} D'] {Θ : PDF R D} {Θ' : PDF R D'}
  {P : ObjectProperty D} {P' : ObjectProperty D'}

def rA (Θ : PDF R D) {P Q : ObjectProperty D} (h : Q ≤ P) :
    CH.Mor (CH.modF (Θ.res P.ι).A) (CH.modF (Θ.res Q.ι).A) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

def rQ (Θ : PDF R D) {P Q : ObjectProperty D} (h : Q ≤ P) (c : R) :
    CH.Mor (sq (IdF.top (Θ.res P.ι).A) (IdF.span (Θ.res P.ι).A c)) (sq (IdF.top (Θ.res Q.ι).A) (IdF.span (Θ.res Q.ι).A c))
      (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem bij_of_sub {c : R} (m : QMor (Θ.res P.ι) (Θ'.res P'.ι) (IdF.span _ c)) (Q : ObjectProperty D) (Q' : ObjectProperty D')
    (hQ : Q ≤ P) (hQ' : Q' ≤ P') (hG : ∀ T : Q'.FullSubcategory, Q (m.G.obj ⟨T.obj, hQ' _ T.property⟩).obj) (j : ℕ)
    (z0 : Function.Bijective ((rA Θ hQ).pull j)) (zq : Function.Bijective ((rQ Θ' hQ' c).pull j))
    (g : Function.Bijective (((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl).pull j)) :
    Function.Bijective ((m.o (IdF.span _ c) fun _ => le_rfl).pull j) := by
  refine (Function.Bijective.of_comp_iff' zq _).1 ?_
  have e : ⇑((rQ Θ' hQ' c).pull j) ∘ ⇑((m.o (IdF.span _ c) fun _ => le_rfl).pull j) =
      ⇑(((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl).pull j) ∘ ⇑((rA Θ hQ).pull j) := by
    funext x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (m.o (IdF.span _ c) fun _ => le_rfl) (rQ Θ' hQ' c) j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (rA Θ hQ)
        ((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl) j x).1))
    rfl
  rw [e]
  exact g.comp z0

end CrystallineSemistableComparison.Pb.SubquotientResolution
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.BijCov

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.SubquotientResolution

open CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.LsQ

section Q

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k)



theorem bij_cov (U : Cov q) {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    Function.Bijective (((mq (F := B.schFn q) (ρ := ρ) hn).o (IdF.span _ ((l : WittVector l k) ^ n))
      (fun _ => le_rfl)).pull j) := by
  have hUs : sSup (Set.range U.U) = ⊤ := by
    rw [sSup_range]
    exact U.cover
  have g := GlobalTheory.T.witt_level_morphism_cover_compat q ρ U n ((l : WittVector l k) ^ n) (mq (F := B.schFn q) (ρ := ρ) hn) (hGq q ρ hn)
    (fun S hS j => by
      obtain ⟨α, hα⟩ := hS
      obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα : (⨅ α ∈ S, U.U α) ≤ U.U α) (U.inter S ⟨α, hα⟩)
      exact GlobalTheory.T.witt_coord_quotient_pull_bijective q ρ hn c' j) j
  have z0 := GlobalTheory.T.witt_site_restrict_bijective q ρ n (Set.range U.U) hUs j
  have zq := GlobalTheory.T.witt_site_quotient_restrict_bijective q ρ (n + 1) (Set.range U.U) ((l : WittVector l k) ^ n) hUs j
  exact bij_of_sub (mq (F := B.schFn q) (ρ := ρ) hn) (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1)
    (fun _ h => h.1) (hGq q ρ hn _) j z0 zq g

end Q



theorem bij : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm →
    ∀ (n : ℕ) (hn : n ≠ 0) (j : ℕ), Function.Bijective (((mq (F := B.schFn M.p) (ρ := r.ρ) hn).o
      (IdF.span _ ((l : WittVector l r.k) ^ n)) (fun _ => le_rfl)).pull j) := by
  intro l _ K r M hM n hn j
  have : IsProper M.p := GlobalTheory.CommonModel.isProper_of_isProjOver hM.1.1
  obtain ⟨U⟩ := (cov_ex M.p).1 hM.2
  exact bij_cov M.p r.ρ U hn j

end CrystallineSemistableComparison.Pb.SubquotientResolution

end
end
end
