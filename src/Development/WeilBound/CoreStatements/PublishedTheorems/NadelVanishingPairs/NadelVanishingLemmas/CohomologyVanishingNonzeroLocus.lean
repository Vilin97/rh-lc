module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsResMEqMulSecOfEqZpowSec
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComplexDirectLimit

section

@[expose] public section

open CategoryTheory Limits Filter

namespace GlobalTheory

namespace CubeColim

variable {ι : Type} [LinearOrder ι] [Fintype ι]

theorem termMap_comp {X Y Z : Cube.{0} ι ℤ} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℕ)
    (x : Cube.Term X p) :
    Cube.termMap (f ≫ g) p x = Cube.termMap g p (Cube.termMap f p x) := rfl

theorem trans_congr {A : ℕ → Cube.{0} ι ℤ} (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d))
    {j j' c d : ℕ} (h : c + j = d) (h' : c + j' = d) (e : j = j') : μ j c d h = μ j' c d h' := by
  subst e; rfl

theorem nonempty_of_card {m : ℕ} (hm : 0 < m) (s : {s : Finset ι // s.card = m}) :
    s.1.Nonempty :=
  Finset.card_pos.1 (by rw [s.2]; exact hm)

theorem exists_lift {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h1 : ∀ j c d h, μ j c d h ≫ ρ d = ρ c)
    (h3 : ∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b)
    {m : ℕ} (hm : 0 < m) (z : Cube.Term B m) :
    ∃ C, ∃ a : Cube.Term (A C) m, Cube.termMap (ρ C) m a = z := by
  choose c a ha using fun s : {s : Finset ι // s.card = m} => h3 s.1 (nonempty_of_card hm s) (z s)
  have hc : ∀ s, c s + (Finset.univ.sup c - c s) = Finset.univ.sup c := fun s => by
    have := Finset.le_sup (f := c) (Finset.mem_univ s); omega
  refine ⟨Finset.univ.sup c,
    fun s => ((μ _ (c s) _ (hc s)).app s.1).hom (a s), funext fun s => ?_⟩
  have e := congrArg (fun f => (f.app s.1).hom (a s)) (h1 _ (c s) _ (hc s))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  rw [Cube.termMap_apply, e]
  exact ha s

theorem exists_kill {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h2 : ∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e),
      μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'')
    (h4 : ∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 →
      ∃ j, (μ j c (c + j) rfl).app s a = 0)
    {m : ℕ} (hm : 0 < m) (c : ℕ) (x : Cube.Term (A c) m) (hx : Cube.termMap (ρ c) m x = 0) :
    ∃ J, Cube.termMap (μ J c (c + J) rfl) m x = 0 := by
  choose j hj using fun s : {s : Finset ι // s.card = m} =>
    h4 s.1 (nonempty_of_card hm s) c (x s) (congrFun hx s)
  refine ⟨Finset.univ.sup j, funext fun s => ?_⟩
  have hle := Finset.le_sup (f := j) (Finset.mem_univ s)
  have hcomp := h2 (j s) (Finset.univ.sup j - j s) c (c + j s) (c + Finset.univ.sup j) rfl
    (by omega) (by omega)
  have e : μ (Finset.univ.sup j) c (c + Finset.univ.sup j) rfl =
      μ (j s + (Finset.univ.sup j - j s)) c (c + Finset.univ.sup j) (by omega) :=
    trans_congr μ _ _ (by omega)
  rw [Cube.termMap_apply, e, ← hcomp]
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  have e : ((μ (j s) c (c + j s) rfl).app s.1).hom (x s) = 0 := hj s
  rw [e, map_zero]
  rfl

theorem exists_cocycle_lift {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h1 : ∀ j c d h, μ j c d h ≫ ρ d = ρ c)
    (h2 : ∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e),
      μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'')
    (h3 : ∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b)
    (h4 : ∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 →
      ∃ j, (μ j c (c + j) rfl).app s a = 0)
    {m : ℕ} (hm : 0 < m) (z : Cube.Term B m) (hz : Cube.d B m z = 0) :
    ∃ C, ∀ c, C ≤ c → ∃ a : Cube.Term (A c) m,
      Cube.termMap (ρ c) m a = z ∧ Cube.d (A c) m a = 0 := by
  obtain ⟨C₀, a, ha⟩ := exists_lift μ ρ h1 h3 hm z
  have hda : Cube.termMap (ρ C₀) (m + 1) (Cube.d (A C₀) m a) = 0 := by
    rw [Cube.termMap_d, ha, hz]
  obtain ⟨J, hJ⟩ := exists_kill μ ρ h2 h4 (Nat.succ_pos m) C₀ _ hda
  refine ⟨C₀ + J, fun c hc => ⟨Cube.termMap (μ (c - C₀) C₀ c (by omega)) m a, ?_, ?_⟩⟩
  · rw [← termMap_comp, h1, ha]
  · rw [← Cube.termMap_d]
    have e : μ (c - C₀) C₀ c (by omega) =
        μ J C₀ (C₀ + J) rfl ≫ μ (c - C₀ - J) (C₀ + J) c (by omega) := by
      rw [h2 J (c - C₀ - J) C₀ (C₀ + J) c rfl (by omega) (by omega)]
      exact trans_congr μ _ _ (by omega)
    rw [e, termMap_comp, hJ, map_zero]

end CubeColim

theorem cechComplex_homology_isZero_of_colimit :
    ∀ {ι : Type} [LinearOrder ι] [Fintype ι] (A : ℕ → Cube.{0} ι ℤ) (B : Cube.{0} ι ℤ) (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) → (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') → (∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b) → (∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) → ∀ n : ℕ, (∀ᶠ c in atTop, IsZero ((cechComplex (A c)).homology n)) → IsZero ((cechComplex B).homology n) := by
  intro ι _ _ A B μ ρ h1 h2 h3 h4 n hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hn
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  cases n with
  | zero =>
    rw [cochainComplex_exactAt_zero_iff, cechComplex_d B 0]
    change Function.Injective (Cube.d B 1)
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨C, hC⟩ := CubeColim.exists_cocycle_lift μ ρ h1 h2 h3 h4 one_pos z hz
    obtain ⟨a, ha, hda⟩ := hC (max C N) (le_max_left _ _)
    have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (hN (max C N) (le_max_right _ _))
    rw [cochainComplex_exactAt_zero_iff, cechComplex_d _ 0] at hex
    change Function.Injective (Cube.d (A (max C N)) 1) at hex
    rw [injective_iff_map_eq_zero] at hex
    rw [← ha, hex a hda, map_zero]
  | succ p =>
    rw [cechComplex_exactAt_succ_iff]
    intro z
    refine ⟨fun hz => ?_, ?_⟩
    · obtain ⟨C, hC⟩ := CubeColim.exists_cocycle_lift μ ρ h1 h2 h3 h4 (m := p + 2) (by omega) z hz
      obtain ⟨a, ha, hda⟩ := hC (max C N) (le_max_left _ _)
      have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        (hN (max C N) (le_max_right _ _))
      rw [cechComplex_exactAt_succ_iff] at hex
      obtain ⟨y, hy⟩ := (hex a).1 hda
      exact ⟨Cube.termMap (ρ _) (p + 1) y, by rw [← Cube.termMap_d, hy, ha]⟩
    · rintro ⟨y, rfl⟩
      exact Cube.d_d B (p + 1) y

end GlobalTheory
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechComplexDirectLimit

section

@[expose] public section

open CategoryTheory Limits Filter GlobalTheory
theorem _root_.GlobalTheory.T.cech_complex_direct_limit : ∀ {ι : Type} [LinearOrder ι] [Fintype ι] (A : ℕ → Cube.{0} ι ℤ) (B : Cube.{0} ι ℤ) (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) → (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') → (∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b) → (∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) → ∀ n : ℕ, (∀ᶠ c in atTop, IsZero ((cechComplex (A c)).homology n)) → IsZero ((cechComplex B).homology n) := by
  first | exact @_root_.GlobalTheory.cechComplex_homology_isZero_of_colimit | exact _root_.GlobalTheory.cechComplex_homology_isZero_of_colimit | (intros; apply _root_.GlobalTheory.cechComplex_homology_isZero_of_colimit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTwistNonzeroLocusMaps

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace TwistCube

open Twist

variable {X : Scheme.{0}} (F : X.Modules) {L : LB X}

theorem mulSecOfEq_zpowSec_comp (σ : LB.Sec (lbZPow L 1)) {n d e : ℤ} (a b : ℕ)
    (h₁ : n + a * 1 = d) (h₂ : d + b * 1 = e) (h₃ : n + ((a + b : ℕ) : ℤ) * 1 = e) :
    mulSecOfEq F (zpowSec σ a) h₁ ≫ mulSecOfEq F (zpowSec σ b) h₂ =
      mulSecOfEq F (zpowSec σ (a + b)) h₃ := by
  ext V s : 3
  exact mulSecOfEq_zpowSec_app σ rfl h₁ h₂ h₃ s

def powMap (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) : F ⟶ twistZ F L c :=
  (twistZZeroIso F hL).hom ≫ mulSecOfEq F (zpowSec σ c) (by omega)

theorem powMap_comp (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (j c d : ℕ) (h : c + j = d)
    (h' : (c : ℤ) + (j : ℤ) * 1 = d) :
    powMap F hL σ c ≫ mulSecOfEq F (zpowSec σ j) h' = powMap F hL σ d := by
  subst h
  rw [powMap, powMap, Category.assoc, mulSecOfEq_zpowSec_comp F σ c j _ _ (by push_cast; ring)]

theorem bijective_powMap_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {W : X.Opens}
    (hW : W ≤ nonzeroLocus σ) : Function.Bijective ((powMap F hL σ c).app W) := by
  rw [powMap, Scheme.Modules.Hom.comp_app, ConcreteCategory.coe_comp]
  exact (bijective_mulSecOfEq_app hL _ (by omega) (hW.trans (nonzeroLocus_le_zpowSec hL σ c))).comp
    (ConcreteCategory.bijective_of_isIso ((twistZZeroIso F hL).hom.app W))

variable {ι : Type} (U : ι → X.Opens)

theorem isIso_cechCubeMap_powMap (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : IsIso (cechCubeMap ℤ V U (powMap F hL σ c)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun s => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_powMap_app F hL σ c ((cechOpen_le V U s).trans hV)

theorem cechCubeRes_naturality {G : X.Modules} (φ : F ⟶ G) {V : X.Opens} :
    cechCubeMap ℤ ⊤ U φ ≫ cechCubeRes ℤ G (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) =
      cechCubeRes ℤ F (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) ≫ cechCubeMap ℤ V U φ :=
  presheafCubeRes_naturality (sectionsPresheafMap ℤ φ) _

def cubeDiv (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F V U :=
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) ≫
    inv (cechCubeMap ℤ V U (powMap F hL σ c))

theorem cubeDiv_comp (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : cubeDiv F U hL σ c hV ≫ cechCubeMap ℤ V U (powMap F hL σ c) =
      cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) := by
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  simp [cubeDiv]

theorem cubeDiv_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) (s : Finset ι) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s) :
    (cechCubeMap ℤ V U (powMap F hL σ c)).app s ((cubeDiv F U hL σ c hV).app s a) =
      (cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)).app s a := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, cubeDiv_comp]

theorem cechCubeMap_mul_comp_cubeDiv (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (j c d : ℕ)
    (h : c + j = d) (h' : (c : ℤ) + (j : ℤ) * 1 = d) {V : X.Opens} (hV : V ≤ nonzeroLocus σ) :
    cechCubeMap ℤ ⊤ U (mulSecOfEq F (zpowSec σ j) h') ≫ cubeDiv F U hL σ d hV =
      cubeDiv F U hL σ c hV := by
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  haveI := isIso_cechCubeMap_powMap F U hL σ d hV
  unfold cubeDiv
  rw [← Category.assoc, cechCubeRes_naturality, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, IsIso.eq_inv_comp]
  exact congrArg (cechCubeMap ℤ V U) (powMap_comp F hL σ j c d h h')

end TwistCube

end GlobalTheory

theorem GlobalTheory.cechCube_nonzeroLocus_colimit : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens), (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∃ (μ : ∀ (j c d : ℕ), c + j = d → (cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ (twistZ F L d) ⊤ U)) (ρ : ∀ c : ℕ, cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F (nonzeroLocus σ) U), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) ∧ (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') ∧ (∀ s : Finset ι, s.Nonempty → ∀ b : (cechCube ℤ F (nonzeroLocus σ) U).obj s, ∃ c : ℕ, ∃ a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s, (ρ c).app s a = b) ∧ (∀ s : Finset ι, s.Nonempty → ∀ (c : ℕ) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) := by
  intro X F _ L hL σ₀ ι _ _ U hU
  have hVσ : nonzeroLocus σ₀ ≤ nonzeroLocus (Twist.zofSec σ₀) := (Twist.nonzeroLocus_zofSec hL σ₀).ge
  refine ⟨fun j c d h => cechCubeMap ℤ ⊤ U
      (Twist.mulSecOfEq F (Twist.zpowSec (Twist.zofSec σ₀) j) (by omega)),
    fun c => TwistCube.cubeDiv F U hL (Twist.zofSec σ₀) c hVσ, ?_, ?_, ?_, ?_⟩
  · intro j c d h
    exact TwistCube.cechCubeMap_mul_comp_cubeDiv F U hL _ j c d h _ hVσ
  · intro j j' c d e h h' h''
    exact congrArg (cechCubeMap ℤ ⊤ U) (TwistCube.mulSecOfEq_zpowSec_comp F _ j j' (by omega) _ _)
  · intro s hs b
    have hA : IsAffineOpen (cechOpen ⊤ U s) := by rw [cechOpen_top]; exact hU s hs
    have hle : cechOpen (nonzeroLocus σ₀) U s ≤ cechOpen ⊤ U s :=
      cechOpen_mono le_top (fun _ => le_rfl) s
    have hV : cechOpen (nonzeroLocus σ₀) U s =
        cechOpen ⊤ U s ⊓ nonzeroLocus (Twist.zofSec σ₀) := by
      rw [cechOpen, cechOpen, top_inf_eq, Twist.nonzeroLocus_zofSec hL, inf_comm]
    obtain ⟨k, hk⟩ := (Twist.eventually_exists_resM_eq_mulSecOfEq_zpowSec hL (Twist.zofSec σ₀)
      hA.isCompact hA.isQuasiSeparated hle hV ((Twist.twistZZeroIso F hL).hom.app _ b)).exists
    obtain ⟨a, ha⟩ := hk k (by omega)
    exact ⟨k, a, (TwistCube.bijective_powMap_app F hL _ k ((cechOpen_le _ U s).trans hVσ)).1
      ((TwistCube.cubeDiv_app F U hL (Twist.zofSec σ₀) k hVσ s a).trans ha)⟩
  · intro s hs c a ha
    have hA : IsAffineOpen (cechOpen ⊤ U s) := by rw [cechOpen_top]; exact hU s hs
    have hle : cechOpen (nonzeroLocus σ₀) U s ≤ cechOpen ⊤ U s :=
      cechOpen_mono le_top (fun _ => le_rfl) s
    have hV : cechOpen (nonzeroLocus σ₀) U s =
        cechOpen ⊤ U s ⊓ nonzeroLocus (Twist.zofSec σ₀) := by
      rw [cechOpen, cechOpen, top_inf_eq, Twist.nonzeroLocus_zofSec hL, inf_comm]
    have h0 : Twist.resM _ hle a = 0 := by
      have e := TwistCube.cubeDiv_app F U hL (Twist.zofSec σ₀) c hVσ s a
      rw [ha, map_zero] at e
      exact e.symm
    obtain ⟨k, hk⟩ := (Twist.eventually_mulSecOfEq_zpowSec_eq_zero hL (Twist.zofSec σ₀)
      hA.isCompact hle hV.ge a h0).exists
    exact ⟨k, hk _ (by push_cast; ring)⟩
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechTwistNonzeroLocusMaps

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory
theorem _root_.GlobalTheory.T.cech_twist_nonzero_locus_maps : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens), (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∃ (μ : ∀ (j c d : ℕ), c + j = d → (cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ (twistZ F L d) ⊤ U)) (ρ : ∀ c : ℕ, cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F (nonzeroLocus σ) U), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) ∧ (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') ∧ (∀ s : Finset ι, s.Nonempty → ∀ b : (cechCube ℤ F (nonzeroLocus σ) U).obj s, ∃ c : ℕ, ∃ a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s, (ρ c).app s a = b) ∧ (∀ s : Finset ι, s.Nonempty → ∀ (c : ℕ) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) := by
  first | exact @_root_.GlobalTheory.cechCube_nonzeroLocus_colimit | exact _root_.GlobalTheory.cechCube_nonzeroLocus_colimit | (intros; apply _root_.GlobalTheory.cechCube_nonzeroLocus_colimit <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingNonzeroLocus

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section
namespace GlobalTheory

theorem isZero_cechH_nonzeroLocus_of_eventually_twist : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec)
    {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens),
    (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∀ n : ℕ,
    (∀ᶠ c : ℕ in atTop, IsZero (cechH ℤ (twistZ F L c) ⊤ U n)) → IsZero (cechH ℤ F (nonzeroLocus σ) U n) := by
  intro X F _ L hL σ ι _ _ U hU n h
  obtain ⟨μ, ρ, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.cech_twist_nonzero_locus_maps X F L hL σ U hU
  exact GlobalTheory.T.cech_complex_direct_limit (fun c => cechCube ℤ (twistZ F L c) ⊤ U) (cechCube ℤ F (nonzeroLocus σ) U) μ ρ h₁ h₂ h₃ h₄ n h

theorem subsingleton_cohOn_nonzeroLocus_of_eventually_twist : ∀ (X : Scheme.{0}) [CompactSpace X] [X.IsSeparated] (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) (i : ℕ), (∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow L c)) i)) → Subsingleton (cohOn F (nonzeroLocus σ) i) := by
  intro X _ _ F _ L hL σ i h
  obtain ⟨κ, hκ, T, c, hT, -, hTc, hcov⟩ :=
    Twist.exists_finite_affine_chart_cover hL (W := ⊤) (isCompact_univ (X := X))
  letI : Fintype κ := Fintype.ofFinite κ
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  have hsep : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ a ∈ s, T a) :=
    (cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).1 (Or.inl inferInstance) κ T hT
  have hc : ⨆ a, T a = ⊤ := eq_top_iff.2 hcov
  have hV : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (cechOpen (nonzeroLocus σ) T s) := by
    rintro s ⟨a, ha⟩
    have hle : ⨅ b ∈ s, T b ≤ L.U (c a) := (biInf_le T ha).trans (hTc a)
    have e := Twist.basicOpen_resG_zfun (Twist.zofSec σ) (c a) hle
    rw [Twist.nonzeroLocus_zofSec hL] at e
    have e' : cechOpen (nonzeroLocus σ) T s = X.basicOpen (resG X hle (Twist.zfun (Twist.zofSec σ) (c a))) := by
      rw [e, cechOpen, inf_comm]
    rw [e']
    exact (hsep s ⟨a, ha⟩).basicOpen _
  have hVc : nonzeroLocus σ ≤ ⨆ a, T a := hc ▸ le_top
  have eV := cechHEquivCohOn ℤ hVc (cechAcyclicMod_of_isAffineOpen hV F) i
  have hZ : IsZero (cechH ℤ F (nonzeroLocus σ) T i) := by
    refine isZero_cechH_nonzeroLocus_of_eventually_twist X F L hL σ T hsep i (h.mono fun k hk => ?_)
    haveI hq : (twistZ F L k).IsQuasicoherent := Twist.isQuasicoherent_twist (Twist.isLB_lbZPow hL k)
    have e2 := cechHEquivCoh ℤ hc hsep (twistZ F L k) i
    haveI : Subsingleton (coh (twistZ F L k) i) := by rw [Twist.twistZ_natCast]; exact hk
    haveI : Subsingleton (cechH ℤ (twistZ F L k) ⊤ T i) := e2.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  haveI : Subsingleton (cechH ℤ F (nonzeroLocus σ) T i) := ModuleCat.subsingleton_of_isZero hZ
  exact eV.symm.injective.subsingleton

end GlobalTheory
end
end
end
