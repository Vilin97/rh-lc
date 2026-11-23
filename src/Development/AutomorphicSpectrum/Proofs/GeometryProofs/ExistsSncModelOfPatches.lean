module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryGeneratorUnitStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsCoordsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeGivesComponent
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGivesChartPrimeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisAdjoinInverseStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationsEqualBasicOpensStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingDeterminesComponentStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelFromLocalPatchesStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeGivesComponentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.chart_prime_gives_component : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothAdjoinInverse

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem isLocalizationAway_invAdj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : Subalgebra ℚ Ω} {g : Ω}
    (hg : g ∈ A) (h0 : g ≠ 0) :
    letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
    IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := by
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  have hmap : ∀ a : A, ((algebraMap A (invAdj A g) a : invAdj A g) : Ω) = a := fun _ => rfl
  refine IsLocalization.Away.mk (⟨g, hg⟩ : A) ?_ ?_ ?_
  · refine IsUnit.of_mul_eq_one (⟨g⁻¹, inv_mem_invAdj A g⟩ : invAdj A g) (Subtype.ext ?_)
    simp [hmap, h0]
  · intro s
    obtain ⟨k, hk⟩ := exists_mul_pow_mem hg h0 s.2
    refine ⟨k, ⟨_, hk⟩, Subtype.ext ?_⟩
    simp [hmap]
  · intro a b hab
    have hab' : a = b := Subtype.ext (by simpa [hmap] using congrArg Subtype.val hab)
    exact ⟨0, by rw [hab']⟩

theorem smooth_invAdj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 →
    Algebra.Smooth ℚ A → Algebra.Smooth ℚ (invAdj A g) := by
  intro Ω _ _ A g hg h0 hA
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ A (invAdj A g) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := isLocalizationAway_invAdj hg h0
  haveI : Algebra.Smooth A (invAdj A g) := Algebra.Smooth.of_isLocalization_Away (⟨g, hg⟩ : A)
  exact Algebra.Smooth.comp ℚ A (invAdj A g)

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothAdjoinInverseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.smooth_adjoin_inverse : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 → Algebra.Smooth ℚ A → Algebra.Smooth ℚ (Mdl.invAdj A g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchBoundaryUnits

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem unitAt_finsetProd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {p : Cpt ξ}
    {I : Type} (s : Finset I) (f : I → Ω) (hf : ∀ i ∈ s, unitAt ξ p (f i)) :
    unitAt ξ p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitAt_one ξ p
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact unitAt_mul (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem unitAt_of_finsetProd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {p : Cpt ξ}
    {I : Type} (s : Finset I) (f : I → Ω) (hf : ∀ i ∈ s, f i ∈ regAt ξ p)
    (hu : unitAt ξ p (∏ i ∈ s, f i)) {i : I} (hi : i ∈ s) : unitAt ξ p (f i) := by
  classical
  rw [← Finset.mul_prod_erase s f hi] at hu
  exact unitAt_of_mul_left hu (hf i hi)
    (prod_mem fun j hj => hf j (Finset.mem_of_mem_erase hj))

theorem exists_chartQ_unit_sep (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    (κ : Type) (x : κ → Ω) (c : κ) (B : Set (Cpt ξ)) (h : Ω) (e n : ℕ)
    (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (p : Cpt ξ) (_hξ : IsCptGen ξ)
    (hB : ∀ q ∈ B, Char0 ξ q) (hh : h ∈ Mdl.chartQ x c) (h0 : h ≠ 0)
    (hcl : ∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h →
      (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω)))
    (hp : Char0 ξ p) (hpc : InChart ξ x c p) (hph : unitAt ξ p h) (hpB : p ∉ B) :
    ∃ a ∈ Mdl.chartQ x c, unitAt ξ p a ∧ ∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a := by
  classical
  set S : Finset (Fin e) := Finset.univ.filter fun i => (i : ℕ) < n with hS
  set f : Fin e → Ω := fun i => (z i : Ω) with hf
  set ζ : Ω := ∏ i ∈ S, f i with hζ
  have hζm : ζ ∈ Mdl.invAdj (Mdl.chartQ x c) h :=
    Subalgebra.prod_mem _ fun i _ => (z i).2
  obtain ⟨m, hm⟩ := exists_mul_pow_mem hh h0 hζm
  refine ⟨ζ * h ^ m * h, (Mdl.chartQ x c).mul_mem hm hh, ?_, ?_⟩
  · have hz : ∀ i ∈ S, unitAt ξ p (f i) := by
      intro i hi
      by_contra hni
      exact hpB ((hcl p hp hpc hph).2 ⟨i, (Finset.mem_filter.1 hi).2, hni⟩)
    exact unitAt_mul (unitAt_mul (unitAt_finsetProd S f hz) (unitAt_pow hph m)) hph
  · intro q hq hqc hua
    have hq0 := hB q hq
    have hA : ∀ s ∈ Mdl.chartQ x c, s ∈ regAt ξ q := fun s hs => chartQ_le hq0 hqc hs
    by_cases hqh : unitAt ξ q h
    · obtain ⟨i, hin, hni⟩ := (hcl q hq0 hqc hqh).1 hq
      have hreg : ∀ j ∈ S, f j ∈ regAt ξ q := fun j _ => invAdj_le hq0 hA hqh (z j).2
      have hζr : ζ ∈ regAt ξ q := prod_mem hreg
      have hhm : h ^ m * h ∈ regAt ξ q := (regAt ξ q).mul_mem (pow_mem (hA h hh) m) (hA h hh)
      have hua' : unitAt ξ q (ζ * (h ^ m * h)) := by rwa [← _root_.mul_assoc]
      have hζu : unitAt ξ q ζ := unitAt_of_mul_left hua' hζr hhm
      exact hni (unitAt_of_finsetProd S f hreg hζu (Finset.mem_filter.2 ⟨Finset.mem_univ i, hin⟩))
    · exact hqh (unitAt_of_mul_right hua (hA _ hm) (hA h hh))

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchBoundaryUnitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.snc_patch_boundary_units : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ) (B : Set (Cpt ξ)) (h : Ω) (e n : ℕ) (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (p : Cpt ξ), IsCptGen ξ → (∀ q ∈ B, Char0 ξ q) → h ∈ Mdl.chartQ x c → h ≠ 0 → (∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h → (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω))) → Char0 ξ p → InChart ξ x c p → unitAt ξ p h → p ∉ B → ∃ a ∈ Mdl.chartQ x c, unitAt ξ p a ∧ ∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSncModelOfPatches

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem ratEval_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ} {x : Fin (N + 1) → Ω}
    {c : Fin (N + 1)} {p : Cpt ξ} (hc : InChart ξ x c p) (g : MRing (fun _ : Unit => Fin (N + 1))) :
    ratEval x c g ∈ regAt ξ p := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem (regAt ξ p) a
  | add a b ha hb => simpa using (regAt ξ p).add_mem ha hb
  | mul_X a i ha =>
    simpa using (regAt ξ p).mul_mem ha (hc.2 i.2)

theorem not_unitAt_of_mem_span {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ}
    {x : Fin (N + 1) → Ω} {B : Set (Cpt ξ)} (hξ : IsCptGen ξ) {c : Fin (N + 1)} {p : Cpt ξ} (hp : p ∈ B)
    (hc : InChart ξ x c p) {g : MRing (fun _ : Unit => Fin (N + 1))} (hg : g ∈ Ideal.span (bdGens ξ x B)) :
    ¬ unitAt ξ p (ratEval x c g) := by
  induction hg using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨d, -, h⟩ := hG
    exact h c p hp hc
  | zero => simpa [unitAt] using fun h : (0 : Ω) ≠ 0 => absurd rfl h
  | add a b _ _ ha hb =>
    have := not_unitAt_add hξ (ratEval_mem hc a) (ratEval_mem hc b) ha hb
    simpa using this
  | smul a b _ hb =>
    intro h
    have e : ratEval x c (a • b) = ratEval x c a * ratEval x c b := by simp
    rw [e] at h
    exact hb (unitAt_of_mul_right h (ratEval_mem hc a) (ratEval_mem hc b))

theorem patch_invAdj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {Pt Bd : Set (Subring Ω)} {e : ℕ} {A : Subalgebra ℚ Ω}
    {z : Fin e → A} {n : ℕ} (hA : IsSncPatch Pt Bd e A z n) {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) :
    ∃ z' : Fin e → invAdj A g, IsSncPatch Pt Bd e (invAdj A g) z' n ∧ ∀ i, (z' i : Ω) = z i := by
  let z' : Fin e → invAdj A g := fun i => ⟨z i, le_invAdj A g (z i).2⟩
  have hd := GlobalTheory.T.kaehler_basis_adjoin_inverse Ω A g hg h0 e z z' (fun _ => rfl) hA.li hA.span
  refine ⟨z', ⟨?_, GlobalTheory.T.smooth_adjoin_inverse Ω A g hg h0 hA.smooth, hA.le, hd.1, hd.2, ?_⟩, fun _ => rfl⟩
  · obtain ⟨S, hS⟩ := hA.fg
    classical
    refine ⟨insert g⁻¹ S, ?_⟩
    rw [Finset.coe_insert]
    apply le_antisymm
    · refine Algebra.adjoin_mono (Set.insert_subset_insert ?_)
      rw [← hS]
      exact Algebra.subset_adjoin
    · refine Algebra.adjoin_le (Set.insert_subset (Algebra.subset_adjoin (Set.mem_insert _ _)) ?_)
      rw [← hS]
      exact Algebra.adjoin_mono (Set.subset_insert _ _)
  · intro q hq
    obtain ⟨R, hR, hloc, hbd⟩ := hA.pts (primeUnder A g q) (Ideal.comap_isPrime _ _)
    refine ⟨R, hR, isLocAt_invAdj hg h0 hq hloc, hbd.trans ?_⟩
    exact exists_congr fun i => and_congr_right fun _ => Iff.rfl

theorem chartQ_fg {Ω : Type} [Field Ω] [Algebra ℚ Ω] {N : ℕ} (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) :
    (chartQ x c).FG :=
  ⟨(Set.finite_range (fun j => x j / x c)).toFinset, by simp⟩

theorem not_mem_primeUnder {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0)
    {q : Ideal (invAdj A g)} (hq : q.IsPrime) : (⟨g, hg⟩ : A) ∉ primeUnder A g q :=
  not_mem_of_isPrime hg h0 hq

variable {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} {ξ : Sp Ω ⟶ X}

theorem exists_patch {N : ℕ} {x : Fin (N + 1) → Ω} {e : ℕ} {B : Set (Cpt ξ)} (hT : CoordTie ℤ ξ x)
    (hP : ∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
      IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p))
    (c : Fin (N + 1)) (p : Cpt ξ) (hp : Char0 ξ p) (hc : InChart ξ x c p) :
    ∃ h ∈ chartQ x c, unitAt ξ p h ∧ ∃ (z : Fin e → invAdj (chartQ x c) h) (n : ℕ),
      IsSncPatch (Pts ξ) (regAt ξ '' B) e (invAdj (chartQ x c) h) z n := by
  obtain ⟨A, z, n, q, hA, hq, hl⟩ := hP p hp
  obtain ⟨I, hI, hu, hIl⟩ := GlobalTheory.T.component_gives_chart_prime Ω X ξ _ x c hT p hp hc
  obtain ⟨g, h, hg, hh, he⟩ := GlobalTheory.T.localizations_equal_basic_opens Ω A (chartQ x c) q I (regAt ξ p) hA.fg (chartQ_fg x c) hq hI hl hIl
  have hg0 : (g : Ω) ≠ 0 := fun h0 => hg (by
    have : g = 0 := Subtype.ext h0
    rw [this]; exact q.zero_mem)
  obtain ⟨z', hz', -⟩ := patch_invAdj hA g.2 hg0
  refine ⟨h, h.2, (hu h).1 hh, ?_⟩
  rw [← he]
  exact ⟨z', n, hz'⟩

theorem primePoint {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) (hx : x c ≠ 0) {h : Ω}
    (hh : h ∈ chartQ x c) (h0 : h ≠ 0) (q : Ideal (invAdj (chartQ x c) h)) (hq : q.IsPrime) :
    ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ unitAt ξ p h ∧
      (∀ s : invAdj (chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (invAdj (chartQ x c) h) q (regAt ξ p) := by
  obtain ⟨p, hp, hc, hu, hl⟩ := GlobalTheory.T.chart_prime_gives_component Ω X ξ κ x c hT hx (primeUnder _ h q) (Ideal.comap_isPrime _ _)
  have hhu : unitAt ξ p h := (hu ⟨h, hh⟩).1 (not_mem_primeUnder hh h0 hq)
  refine ⟨p, hp, hc, hhu, ?_, isLocAt_invAdj hh h0 hq hl⟩
  intro s
  obtain ⟨k, hk⟩ := exists_mul_pow_mem hh h0 s.2
  have hreg : (s : Ω) ∈ regAt ξ p := invAdj_le hp (fun _ => chartQ_le hp hc) hhu s.2
  rw [not_congr (mem_iff_mul_pow hh h0 hq s k ⟨_, hk⟩ rfl), hu]
  exact ⟨fun u => unitAt_of_mul_left u hreg (unitAt_pow hhu k).2.1, fun u => unitAt_mul u (unitAt_pow hhu k)⟩

theorem pointPrime {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) {h : Ω} (hh : h ∈ chartQ x c)
    (p : Cpt ξ) (hp : Char0 ξ p) (hc : InChart ξ x c p) (hu : unitAt ξ p h) :
    ∃ q : Ideal (invAdj (chartQ x c) h), q.IsPrime ∧
      (∀ s : invAdj (chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (invAdj (chartQ x c) h) q (regAt ξ p) := by
  haveI hloc : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hT.gen p).1
  have hmem : ∀ s : invAdj (chartQ x c) h, (s : Ω) ∈ regAt ξ p :=
    fun s => invAdj_le hp (fun _ => chartQ_le hp hc) hu s.2
  let f : invAdj (chartQ x c) h →+* regAt ξ p :=
    ((invAdj (chartQ x c) h).val : invAdj (chartQ x c) h →+* Ω).codRestrict (regAt ξ p) hmem
  have hq : (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))).IsPrime := inferInstance
  have hs : ∀ s : invAdj (chartQ x c) h,
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ p (s : Ω) := by
    intro s
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    constructor
    · intro hu'
      obtain ⟨b, hb⟩ := hu'.exists_right_inv
      have e1 : (s : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (s : Ω) ≠ 0 := fun h0 => by simp [h0] at e1
      refine ⟨h0, hmem s, ?_⟩
      rw [inv_eq_of_mul_eq_one_right e1]
      exact b.2
    · rintro ⟨h0, -, hinv⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  obtain ⟨I, -, hI, hIl⟩ := GlobalTheory.T.component_gives_chart_prime Ω X ξ κ x c hT p hp hc
  have e : primeUnder (chartQ x c) h (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))) = I := by
    ext a
    exact not_iff_not.1 ((hs ⟨a, le_invAdj _ h a.2⟩).trans (hI a).symm)
  exact ⟨_, hq, hs, isLocAt_invAdj hh hu.1 hq (e ▸ hIl)⟩

theorem patchClause {κ : Type} {x : κ → Ω} {e : ℕ} {B : Set (Cpt ξ)} (hT : CoordTie ℤ ξ x)
    {S : Subalgebra ℚ Ω} {z : Fin e → S} {n : ℕ} (hS : IsSncPatch (Pts ξ) (regAt ξ '' B) e S z n)
    (q : Ideal S) (hq : q.IsPrime) (p : Cpt ξ) (hl : IsLocAt S q (regAt ξ p)) :
    p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q := by
  obtain ⟨R, -, hRl, hbd⟩ := hS.pts q hq
  have hR : R = regAt ξ p := Subring.ext fun a => (hRl a).trans (hl a).symm
  subst hR
  rw [← hbd]
  constructor
  · exact fun hp => ⟨p, hp, rfl⟩
  · rintro ⟨p', hp', e'⟩
    have := GlobalTheory.T.regular_ring_determines_component X Ω ξ ℤ κ x hT p' p e'
    exact this ▸ hp'

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

namespace GlobalTheory.CompanionTheory.Ar.SncBase


open Mdl in
theorem exists_isSncModel_of_patches : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (B : Set (Cpt ξ)), CoordTie ℤ ξ x → (∀ p ∈ B, Char0 ξ p) → (∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A), IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)) → ∃ bd : Ideal (MRing (fun _ : Unit => Fin (N + 1))), Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w → (w ∈ mcPts bd ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  open Mdl in
  intro Ω _ _ X ξ N x e B hT hB hP
  have hcov := fun c p hp hc => exists_patch (B := B) hT hP c p hp hc
  have hsep : ∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → p ∉ B →
      ∃ G ∈ bdGens ξ x B, unitAt ξ p (ratEval x c G) := by
    intro c p hp hc hnB
    obtain ⟨h, hh, hu, z, n, hz⟩ := hcov c p hp hc
    have hcl : ∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h →
        (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω)) := by
      intro q hq hcq huq
      obtain ⟨Q, hQ, hs, hl⟩ := pointPrime hT hh q hq hcq huq
      rw [patchClause hT hz Q hQ q hl]
      refine exists_congr fun i => and_congr_right fun _ => ?_
      rw [← hs (z i), not_not]
    obtain ⟨a, ha, hau, hnon⟩ := GlobalTheory.T.snc_patch_boundary_units Ω X ξ _ x c B h e n z p hT.gen hB hh hu.1 hcl hp hc hu hnB
    exact GlobalTheory.T.boundary_generator_unit Ω X ξ N x c B p a hB hp hc ha hau hnon
  refine ⟨Ideal.span (bdGens ξ x B), ?_, GlobalTheory.T.boundary_points_coords Ω X ξ N x B hT.gen hsep⟩
  refine GlobalTheory.T.snc_model_from_local_patches Ω X ξ N x e B _ hcov ?_ ?_ ?_
  · intro c hx I hI
    obtain ⟨p, a, b, d, -⟩ := GlobalTheory.T.chart_prime_gives_component Ω X ξ _ x c hT hx I hI
    exact ⟨p, a, b, d⟩
  · intro c h hx hh h0 q hq
    obtain ⟨p, hp, hc, -, hs, hl⟩ := primePoint hT hx hh h0 q hq
    exact ⟨p, hp, hc, hs, fun z n hz => patchClause hT hz q hq p hl⟩
  · intro c p hp hc
    constructor
    · intro hpB g hg
      exact not_unitAt_of_mem_span hT.gen hpB hc hg
    · intro hall
      by_contra hn
      obtain ⟨G, hG, hu⟩ := hsep c p hp hc hn
      exact hall G (Ideal.subset_span hG) hu

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end
end
