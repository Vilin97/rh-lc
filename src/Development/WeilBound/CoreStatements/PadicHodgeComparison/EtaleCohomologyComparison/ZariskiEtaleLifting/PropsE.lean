module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrTeichProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPeriodRingSeparationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantToZModPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversalStatement
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
import Mathlib.Tactic.TypeStar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementProperties
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsQuot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLiftToThickening
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemMapBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSpanIffOfBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepDesc

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrToContInjective

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContLine

variable {l : ℕ} [Fact l.Prime]

theorem toCont_ev (A : PAlg l) (z : ℤ_[l]) : A.toCont ℤ_[l] ≫ A.evCont z = 𝟙 A :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem shift_ev (A : PAlg l) (z : ℤ_[l]) : contShift A ≫ A.evCont z = A.evCont (z + 1) :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem toCont_shift (A : PAlg l) : A.toCont ℤ_[l] ≫ contShift A = A.toCont ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem toCont_contMap {A B : PAlg l} (φ : A ⟶ B) :
    A.toCont ℤ_[l] ≫ contMap φ ℤ_[l] = φ ≫ B.toCont ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_id (A : PAlg l) : contMap (𝟙 A) ℤ_[l] = 𝟙 (A.cont ℤ_[l]) :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_comp {A B C : PAlg l} (φ : A ⟶ B) (ψ : B ⟶ C) :
    contMap (φ ≫ ψ) ℤ_[l] = contMap φ ℤ_[l] ≫ contMap ψ ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_shift {A B : PAlg l} (φ : A ⟶ B) :
    contMap φ ℤ_[l] ≫ contShift B = contShift A ≫ contMap φ ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

def Xi (P : PAlg l ⥤ Type) : P.Elements ⥤ P.Elements where
  obj T := P.elementsMk (T.obj.cont ℤ_[l]) (P.map (T.obj.toCont ℤ_[l]) T.val)
  map {T T'} φ := Functor.Elements.homMk (contMap φ.hom ℤ_[l]) (by
    rw [← Functor.map_comp_apply, toCont_contMap, Functor.map_comp_apply, φ.map_val])
  map_id T := Functor.Elements.hom_ext (contMap_id T.obj)
  map_comp φ ψ := Functor.Elements.hom_ext (contMap_comp φ.hom ψ.hom)

def iota (P : PAlg l ⥤ Type) : 𝟭 P.Elements ⟶ Xi P where
  app T := Functor.Elements.homMk (T.obj.toCont ℤ_[l]) rfl
  naturality T T' φ := Functor.Elements.hom_ext (toCont_contMap φ.hom).symm

def gam (P : PAlg l ⥤ Type) : Xi P ⟶ Xi P where
  app T := Functor.Elements.homMk (contShift T.obj) (by
    change P.map (contShift T.obj) (P.map (T.obj.toCont ℤ_[l]) T.val) =
      P.map (T.obj.toCont ℤ_[l]) T.val
    rw [← Functor.map_comp_apply, toCont_shift])
  naturality T T' φ := Functor.Elements.hom_ext (contMap_shift φ.hom)

def eta₀ (ε : Eps l) : (((base l).cont ℤ_[l]).A)ˣ := (GlobalTheory.T.continuous_algebra_universal_property ε).choose

theorem eta₀_sharp (ε : Eps l) : ((base l).cont ℤ_[l]).sharp (eta₀ ε) = 1 :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.1

theorem eta₀_shift (ε : Eps l) :
    PAlg.Hom.f (contShift (base l)) (eta₀ ε) = ((base l).cont ℤ_[l]).s (ε.e 0) * eta₀ ε :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.2.1

theorem eta₀_univ (ε : Eps l) (A t : PAlg l) (ht : t.IsTest) (φ : A ⟶ t) (u : (t.A)ˣ) (hu : t.sharp u = 1) :
    ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧
      PAlg.Hom.f ψ (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε)) = u :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.2.2 A t ht φ u hu

def eta (ε : Eps l) (A : PAlg l) : ((A.cont ℤ_[l]).A)ˣ :=
  Units.map (PAlg.Hom.f (contMap A.fromBase ℤ_[l])).toMonoidHom (eta₀ ε)

theorem eta_val (ε : Eps l) (A : PAlg l) :
    ((eta ε A : ((A.cont ℤ_[l]).A)ˣ) : (A.cont ℤ_[l]).A) = PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε) := rfl

theorem eta_sharp (ε : Eps l) (A : PAlg l) : (A.cont ℤ_[l]).sharp (eta ε A) = 1 := by
  rw [eta_val, ← mapU_sharp, eta₀_sharp, map_one]

theorem eta_map (ε : Eps l) {A B : PAlg l} (φ : A ⟶ B) :
    PAlg.Hom.f (contMap φ ℤ_[l]) (eta ε A) = eta ε B := by
  rw [eta_val, eta_val, ← fromBase_comp A φ, contMap_comp]
  rfl

theorem eta_shift (ε : Eps l) (A : PAlg l) :
    PAlg.Hom.f (contShift A) (eta ε A) = (A.cont ℤ_[l]).s (ε.e 0) * eta ε A := by
  have h : PAlg.Hom.f (contShift A) (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε)) =
      PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (PAlg.Hom.f (contShift (base l)) (eta₀ ε)) :=
    congrArg (fun f => PAlg.Hom.f f (eta₀ ε)) (contMap_shift A.fromBase).symm ▸ rfl
  rw [eta_val, h, eta₀_shift, map_mul]
  exact congrArg (· * _) (RingHom.congr_fun (Hom.comm (contMap A.fromBase ℤ_[l])) (ε.e 0 : Ob l))

def line (ε : Eps l) (P : PAlg l ⥤ Type) : Line (jE P) (epsU ε P) where
  Ξ := Xi P
  i := iota P
  η T := ⟨eta ε T.obj, MonoidHom.mem_ker.2 (Units.ext (eta_sharp ε T.obj))⟩
  map_η φ := Subtype.ext (Units.ext (eta_map ε φ.hom))
  γ := gam P
  iγ := NatTrans.ext (funext fun T => Functor.Elements.hom_ext (toCont_shift T.obj))
  γη T := Subtype.ext (Units.ext (eta_shift ε T.obj))
  univ T t φ a := by
    have ha : t.obj.obj.sharp (a.1).1 = 1 := congrArg Units.val (MonoidHom.mem_ker.1 a.2)
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := eta₀_univ ε T.obj t.obj.obj t.obj.property φ.hom a.1 ha
    have hψ : P.map ψ (P.map (T.obj.toCont ℤ_[l]) T.val) = t.val := by
      rw [← Functor.map_comp_apply, h1]
      exact φ.map_val
    refine ⟨Functor.Elements.homMk ψ hψ, ⟨Functor.Elements.hom_ext h1, Subtype.ext (Units.ext h2)⟩, ?_⟩
    rintro ⟨ψ', h'⟩ ⟨e1, e2⟩
    refine Functor.Elements.hom_ext (hu ψ' ⟨congrArg Functor.Elements.Hom.hom e1, ?_⟩)
    exact congrArg (fun x => (x.1).1) e2

theorem acr_ev_const (A : PAlg l) (n : ℕ) (z : ℤ_[l]) (a : A.Acr n) :
    mapAcr (A.evCont z) n (mapAcr (A.toCont ℤ_[l]) n a) = a := by
  rw [← mapAcr_comp, toCont_ev, mapAcr_id]

theorem acr_ev_shift (A : PAlg l) (n : ℕ) (z : ℤ_[l]) (x : (A.cont ℤ_[l]).Acr n) :
    mapAcr (A.evCont z) n (mapAcr (contShift A) n x) = mapAcr (A.evCont (z + 1)) n x := by
  rw [← mapAcr_comp, shift_ev]

theorem acr_toCont_injective (A : PAlg l) (n : ℕ) : Function.Injective (mapAcr (A.toCont ℤ_[l]) n) :=
  Function.LeftInverse.injective (g := mapAcr (A.evCont 0) n) (acr_ev_const A n 0)

theorem map_mem_map {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : A.Acr n}
    (hx : x ∈ 𝔞.map (mapAcr A.fromBase n)) : mapAcr f n x ∈ 𝔞.map (mapAcr B.fromBase n) := by
  have h : 𝔞.map (mapAcr A.fromBase n) ≤ (𝔞.map (mapAcr B.fromBase n)).comap (mapAcr f n) :=
    Ideal.map_le_iff_le_comap.2 fun a ha => by
      rw [Ideal.mem_comap, Ideal.mem_comap, mapAcr_fromBase]
      exact Ideal.mem_map_of_mem _ ha
  exact h hx

theorem fixed_const (A : PAlg l) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : (A.cont ℤ_[l]).Acr n}
    (hx : x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n)) (hg : mapAcr (contShift A) n x = x) :
    ∃ m ∈ 𝔞.map (mapAcr A.fromBase n), mapAcr (A.toCont ℤ_[l]) n m = x := by
  obtain ⟨hlc, hinj, -⟩ := GlobalTheory.T.continuous_functions_period_ring_separation A n
  have hper : ∀ z, mapAcr (A.evCont z) n x = mapAcr (A.evCont 0) n x :=
    GlobalTheory.CompanionTheory.PadicShift.eq_of_shift_invariant l _ (hlc x) fun z => by
      rw [← acr_ev_shift, hg]
  refine ⟨mapAcr (A.evCont 0) n x, map_mem_map _ n 𝔞 hx, ?_⟩
  rw [← sub_eq_zero]
  refine hinj _ fun z => ?_
  rw [map_sub, acr_ev_const, hper z, sub_self]

theorem shift_surj (A : PAlg l) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : (A.cont ℤ_[l]).Acr n}
    (hx : x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n)) :
    ∃ y ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n), mapAcr (contShift A) n y - y = x := by
  obtain ⟨hlc, hinj, hex⟩ := GlobalTheory.T.continuous_functions_period_ring_separation A n
  let f : ℤ_[l] → ↥(𝔞.map (mapAcr A.fromBase n)) := fun z =>
    ⟨mapAcr (A.evCont z) n x, map_mem_map _ n 𝔞 hx⟩
  have hf : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun z => ?_
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hlc x) z] with w hw
    exact Subtype.ext hw
  have hN : ∀ a : ↥(𝔞.map (mapAcr A.fromBase n)), l ^ n • a = 0 := fun a => Subtype.ext (by
    change l ^ n • (a.1 : A.Acr n) = 0
    rw [nsmul_eq_mul, Nat.cast_pow, A.pow_l_acr n, zero_mul])
  obtain ⟨y, hy, hd⟩ := GlobalTheory.CompanionTheory.PadicShift.exists_primitive l n hN f hf
  obtain ⟨w, hw, hwz⟩ := hex 𝔞 (fun z => (y z).1) (hy.comp _) fun z => (y z).2
  refine ⟨w, hw, ?_⟩
  rw [← sub_eq_zero]
  refine hinj _ fun z => ?_
  rw [map_sub, map_sub, acr_ev_shift, hwz, hwz, sub_eq_zero]
  exact congrArg Subtype.val (hd z)

theorem facyc_of {R : Type} [CommRing R] {C : Type*} [Category C] {G : C ⥤ ModuleCat.{0} R} (Φ : Flt G) {T T' : C}
    (i : T ⟶ T') (g : T' ⟶ T') (h1 : Function.Injective (G.map i).hom)
    (h2 : ∀ r, ∀ x ∈ (Φ.S r).S T', (G.map g).hom x = x → ∃ m, m ∈ (Φ.S r).S T ∧ (G.map i).hom m = x)
    (h3 : ∀ r, ∀ x ∈ (Φ.S r).S T', ∃ y, y ∈ (Φ.S r).S T' ∧ (G.map g).hom y - y = x) : Φ.FAcyc i g := by
  refine ⟨h1, fun r x hx hg => ?_, fun r x hx => ?_⟩
  · obtain ⟨m, hm, hmx⟩ := h2 r x hx hg
    exact ⟨_, Φ.mul r T m hm, by rw [map_smul, hmx]⟩
  · obtain ⟨y, hy, hyx⟩ := h3 r x hx
    exact ⟨_, Φ.mul r T' y hy, by rw [map_smul, ← smul_sub, hyx]⟩

section Main

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)

theorem mem_step (r : ℕ) (T : (F.pt κ).Elements) (x : T.1.Acr n) :
    x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S T ↔
      x ∈ (fil (DD k (base l) n) (ρ r)).map (mapAcr T.1.fromBase n) := by
  rw [← (GlobalTheory.T.period_ring_base_change_from_universal T.1 n).2.2.2.2.1 k (ρ r)]
  rfl

theorem step_fixed (T : (F.pt κ).Elements) (r : ℕ) (x : (T.1.cont ℤ_[l]).Acr n)
    (hx : x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T))
    (hg : mapAcr (contShift T.1) n x = x) :
    ∃ m : T.1.Acr n, m ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S T ∧
      mapAcr (T.1.toCont ℤ_[l]) n m = x := by
  obtain ⟨m, hm, hmx⟩ := fixed_const T.1 n _ ((mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) x).1 hx) hg
  exact ⟨m, (mem_step F κ ε k n ρ hρ r T m).2 hm, hmx⟩

theorem step_surj (T : (F.pt κ).Elements) (r : ℕ) (x : (T.1.cont ℤ_[l]).Acr n)
    (hx : x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T)) :
    ∃ y : (T.1.cont ℤ_[l]).Acr n, y ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T) ∧
      mapAcr (contShift T.1) n y - y = x := by
  obtain ⟨y, hy, hyx⟩ := shift_surj T.1 n _ ((mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) x).1 hx)
  exact ⟨y, (mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) y).2 hy, hyx⟩

theorem facyc (T : (F.pt κ).Elements) :
    ((flt F κ ε k n ρ hρ).comap (gE F κ k n)).FAcyc ((line ε (F.pt κ)).i.app T) ((line ε (F.pt κ)).γ.app T) :=
  facyc_of _ _ _ (acr_toCont_injective T.1 n) (fun r x hx hg => step_fixed F κ ε k n ρ hρ T r x hx hg)
    (fun r x hx => step_surj F κ ε k n ρ hρ T r x hx)

end Main

theorem exists_line : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), ∃ L : Line (jE (F.pt κ)) (epsU ε (F.pt κ)), ∀ T, ((flt F κ ε k n ρ hρ).comap (gE F κ k n)).FAcyc (L.i.app T) (L.γ.app T) :=
  fun F κ ε k n ρ hρ => ⟨line ε (F.pt κ), facyc F κ ε k n ρ hρ⟩

end GlobalTheory.CompanionTheory.ContLine
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GammaComp

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThetaEx

section Gen
variable {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1)
  {κ : O →+* b.R ⧸ b.I}
  (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i))
  (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R))

theorem arrow_ex (T : Thick (F.cr b ht κ)) (g' : s.R →+* T.B ⧸ T.J)
    (hg' : F.Pt.map (CommRingCat.ofHom g') s.y₀ = T.y.1.2) (u : Fin d → T.B)
    (hu : ∀ k, Ideal.Quotient.mk T.J (u k) = g' (s.T k)) :
    ∃ c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T, ∀ k, c.φ (𝓛.t k) = u k := by
  obtain ⟨g, -, hg, hU⟩ := GlobalTheory.CompanionTheory.ThickHom.main s ht 𝓛 δ hδ hp hn T
  obtain ⟨g₀, -, h₀⟩ := s.univ (CommRingCat.of (T.B ⧸ T.J)) T.y.1.2 (T.y.1.1.comp κ) T.y.2
  have e : g' = g := (h₀ g' hg').trans (h₀ g hg).symm
  subst e
  exact (hU u hu).exists

theorem arrow_uniq (T : Thick (F.cr b ht κ)) (c c' : liftObj s ht 𝓛 δ hδ hp hn ⟶ T)
    (h : ∀ k, c.φ (𝓛.t k) = c'.φ (𝓛.t k)) : c = c' := by
  obtain ⟨g, hc, -, hU⟩ := GlobalTheory.CompanionTheory.ThickHom.main s ht 𝓛 δ hδ hp hn T
  exact (hU (fun k => c'.φ (𝓛.t k)) (fun k => hc c' _ _ (𝓛.hT k).symm)).unique h fun _ => rfl

end Gen

theorem gamma_comp {C C₀ : Type*} [Category C] [Category C₀] {j : C₀ ⥤ C} {U : UF C} {d : ℕ} {D T : C}
    (A : Act j U d D) (a : Gam d) (θ : D ⟶ T) :
    (A.γ a).asHom ≫ θ = A.act (fun k => U.q T ^ (Multiplicative.toAdd a k)) θ := by
  change A.act _ (𝟙 D) ≫ θ = _
  rw [A.act_comp, Category.id_comp]
  congr 1
  funext k
  rw [map_pow, U.map_q]

theorem i_qU {l : ℕ} [Fact l.Prime] (ε : Eps l) (A : PAlg l) (n : ℕ) :
    mapAcr A.fromBase n (ε.qU n : (base l).Acr n) = A.toAcr n (WittVector.teichmuller l (A.s (ε.e 0))) := by
  rw [ε.qU_val, mapAcr_cris, ε.cris_qk]

theorem teich_step {l : ℕ} [Fact l.Prime] (A : PAlg l) (f : A ⟶ A) (n m : ℕ) (e c : A.A)
    (h : Hom.f f c = e ^ m * c) :
    A.toAcr n (WittVector.teichmuller l e) ^ m * A.toAcr n (WittVector.teichmuller l c) =
      mapAcr f n (A.toAcr n (WittVector.teichmuller l c)) := by
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller, h, map_mul, map_pow, map_mul, map_pow]

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (ε : Eps l) (A : Act (𝟭 _) (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)) d (liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)) (A' : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj), (∀ (T : Thick (Lc F κ k n)) (a : Fin d → (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)).U T) (c : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ T) (j : Fin d), (A.act a c).φ (𝓛.t j) = ((a j).1 : T.B) * c.φ (𝓛.t j)) → (∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (j : Fin d), PAlg.Hom.f (A'.act a φ).hom (𝒯.c j 0).val = ((a j).1 : T.1.A) * PAlg.Hom.f φ.hom (𝒯.c j 0).val) → ∃ θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj, (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) ∧ ∀ a, (A.γ a).asHom ≫ θ = θ ≫ (gE F κ k n).map (A'.γ a).asHom := by
  intro l _ O _ F κ d s 𝒯 k n 𝓛 δ hδ hp hn ε A A' hA hA'
  have hy : F.Pt.map (CommRingCat.ofHom ((uJ k 𝒯.A n).comp 𝒯.g)) s.y₀ = ((gE F κ k n).obj 𝒯.obj).y.1.2 := by
    rw [CommRingCat.ofHom_comp, F.Pt.map_comp]
    rfl
  have hu : ∀ j, Ideal.Quotient.mk (JJ k 𝒯.A n) (𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) =
      (uJ k 𝒯.A n).comp 𝒯.g (s.T j) := fun j => by
    rw [RingHom.comp_apply, ← 𝒯.c_sharp j]
    exact (uJ_th k 𝒯.A n _).symm
  obtain ⟨θ, hθ⟩ := arrow_ex s rfl 𝓛 δ hδ hp hn ((gE F κ k n).obj 𝒯.obj) ((uJ k 𝒯.A n).comp 𝒯.g) hy
    (fun j => 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) hu
  refine ⟨θ, hθ, fun a => arrow_uniq s rfl 𝓛 δ hδ hp hn _ _ _ fun j => ?_⟩
  have h1 : ((A.γ a).asHom ≫ θ).φ (𝓛.t j) =
      𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.A.s (ε.e 0))) ^ (Multiplicative.toAdd a j) *
        𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A)) := by
    rw [gamma_comp A a θ, hA _ _ θ j, hθ j, ← i_qU]
    rfl
  have h2 : PAlg.Hom.f (A'.γ a).asHom.hom (𝒯.c j 0).val =
      (𝒯.A.s (ε.e 0)) ^ (Multiplicative.toAdd a j) * (𝒯.c j 0).val := hA' 𝒯.obj _ (𝟙 𝒯.obj) j
  have h3 : (θ ≫ (gE F κ k n).map (A'.γ a).asHom).φ (𝓛.t j) =
      mapAcr (A'.γ a).asHom.hom n (𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) :=
    congrArg (mapAcr (A'.γ a).asHom.hom n) (hθ j)
  rw [h1, h3]
  exact teich_step 𝒯.A _ n _ _ _ h2

end GlobalTheory.CompanionTheory.ThetaEx
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IncPtInjective

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ElOnto

variable {l : ℕ} [Fact l.Prime]

theorem elMap_full {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (hu : ∀ A, Function.Injective (u.app A)) : (elMap u).Full := by
  refine ⟨fun {X Y} f => ⟨⟨f.1, ?_⟩, rfl⟩⟩
  apply hu
  exact (NatTrans.naturality_apply u ((testι l).map f.1) X.2).trans f.2

theorem elMap_faithful {P P' : PAlg l ⥤ Type} (u : P ⟶ P') : (elMap u).Faithful := by
  refine ⟨fun {X Y} f g h => Functor.Elements.Hom.ext ?_⟩
  have h' := congrArg (fun f => f.hom) h
  exact h'

variable {O : Type} [CommRing O]

theorem inc_pt_injective {F : Fn O} (κ : O →+* OC l) (V : F.Sub) (A : PAlg l) :
    Function.Injective ((V.inc.pt κ).app A) := by
  intro a b h
  have h' := congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  exact h'

theorem onto_subEl : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (S : Set 𝒜.A) (k : Bool) (n : ℕ), n ≠ 0 → Onto (subEl κ (Fn.Sub.inter 𝒜.V S)) fun T => ∀ α ∈ S, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 := by
  intro l _ O _ F κ d 𝒜 S k n hn
  refine ⟨elMap_full _ (inc_pt_injective κ _), elMap_faithful _, ?_, ?_⟩
  · intro T α hα
    exact (𝒜.V α).in_map _ (T.2.1.2 α hα)
  · intro T hT
    obtain ⟨hs, hj⟩ := (GlobalTheory.T.period_ring_base_change_from_universal T.1.obj n).2.2.2.2.2.2 k hn
    refine ⟨⟨⟨⟨T.2.1, fun α hα => 𝒜.jac α _ _ (CommRingCat.ofHom (uJ k T.1.obj n)) T.2.1 hs hj (hT α hα)⟩, T.2.2⟩⟩, ⟨Iso.refl _⟩⟩

end GlobalTheory.CompanionTheory.ElOnto
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsE

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.eps_facts : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) :=
  @GlobalTheory.CompanionTheory.EpsFacts.eps_facts

theorem CrystallineSemistableComparison.B.P.cont_line : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), ∃ L : Line (jE (F.pt κ)) (epsU ε (F.pt κ)), ∀ T, ((flt F κ ε k n ρ hρ).comap (gE F κ k n)).FAcyc (L.i.app T) (L.γ.app T) :=
  @GlobalTheory.CompanionTheory.ContLine.exists_line

theorem CrystallineSemistableComparison.B.P.tower_ex : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} (κ : O →+* OC l) {d : ℕ} (s : F.Small d), Nonempty (Tower κ s) :=
  @GlobalTheory.CompanionTheory.TowerEx.tower_ex

theorem CrystallineSemistableComparison.B.P.tower_act : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (ε : Eps l), ∃ A : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj, ∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d), PAlg.Hom.f (A.act a φ).1 (𝒯.c k 0).val = ((a k).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c k 0).val :=
  @GlobalTheory.CompanionTheory.TowerAct.tower_act

theorem CrystallineSemistableComparison.B.P.theta_ex : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (ε : Eps l) (A : Act (𝟭 _) (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)) d (liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)) (A' : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj), (∀ (T : Thick (Lc F κ k n)) (a : Fin d → (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)).U T) (c : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ T) (j : Fin d), (A.act a c).φ (𝓛.t j) = ((a j).1 : T.B) * c.φ (𝓛.t j)) → (∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (j : Fin d), PAlg.Hom.f (A'.act a φ).1 (𝒯.c j 0).val = ((a j).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c j 0).val) → ∃ θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj, (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) ∧ ∀ a, (A.γ a).asHom ≫ θ = θ ≫ (gE F κ k n).map (A'.γ a).asHom :=
  @GlobalTheory.CompanionTheory.ThetaEx.main

theorem CrystallineSemistableComparison.B.P.local_ni : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (ε : Eps l) (ρ : ℕ → ℕ) (hρ : Slow ρ) (γ : Gam d →* End (liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)) (γ' : Gam d →* End 𝒯.obj) (θ : SingleObj.functor γ ⟶ SingleObj.functor γ' ⋙ gE F κ k n), n ≠ 0 → (∀ j, (θ.app (SingleObj.star _)).φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) → (∀ a j, Thick.Hom.φ (γ a).asHom (𝓛.t j) = 𝓛.i (ε.qU n) ^ (Multiplicative.toAdd a j) * 𝓛.t j) → (∀ a j, PAlg.Hom.f (A := 𝒯.A) (B := 𝒯.A) (γ' a).asHom.1 (𝒯.c j 0).val = 𝒯.A.s (ε.e 0) ^ (Multiplicative.toAdd a j) * (𝒯.c j 0).val) → Nonempty (NI (Polynomial.X : Polynomial ℤ) (Functor.whiskerRight θ (flt F κ ε k n ρ hρ).rees)) :=
  @GlobalTheory.CompanionTheory.TowerNI.main

theorem CrystallineSemistableComparison.B.P.desc : ∀ {l : ℕ} [Fact l.Prime], D.Out l → ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), (k = false ∨ ρ = 0) → Desc (Polynomial.X : Polynomial ℤ) (gE F κ k n ⋙ (flt F κ ε k n ρ hρ).rees) (jE (F.pt κ)) :=
  @GlobalTheory.CompanionTheory.DescTest.main

theorem CrystallineSemistableComparison.B.P.el_zar : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (k : Bool) (n r : ℕ), ZarCov (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) fun T => ∃ α, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 :=
  @GlobalTheory.CompanionTheory.TestZar.zarCov_test

theorem CrystallineSemistableComparison.B.P.el_onto : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (S : Set 𝒜.A) (k : Bool) (n : ℕ), n ≠ 0 → Onto (subEl κ (Fn.Sub.inter 𝒜.V S)) fun T => ∀ α ∈ S, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 :=
  @GlobalTheory.CompanionTheory.ElOnto.onto_subEl
end
end
