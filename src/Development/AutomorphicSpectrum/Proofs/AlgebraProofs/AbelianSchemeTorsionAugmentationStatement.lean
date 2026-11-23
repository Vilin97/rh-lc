module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsAddEquiv
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
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderPullbackAlongHomStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsFiniteFlatSubgroupStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHomomorphismCompatibleStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrderStatement
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.TensorSpan

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.RhPull

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

theorem sub_pull : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K := by
  intro p C _ R _ _ N N' _ _ M M' j K hM hG g hg
  rw [← hM] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  have hinv : g' ∈ invFun M' ⊥ := ⟨hg', fun x k hk => by rw [AddSubgroup.mem_bot.1 hk, add_zero]⟩
  have h1 : g' ∈ Algebra.adjoin R ((afFun p (invFun M' ⊥) : Submodule R (N' → C)) : Set (N' → C)) :=
    hG hinv
  change (fun x => g' (j x)) ∈
    Algebra.adjoin R ((afFun p (invFun M K) : Submodule R (N → C)) : Set (N → C))
  clear hg' hinv
  induction h1 using Algebra.adjoin_induction with
  | mem f hf =>
    refine Algebra.subset_adjoin ⟨?_, fun x y => ?_⟩
    · rw [← hM]
      exact ⟨f, hf.1.1, rfl⟩
    · have := hf.2 (j x) (j y)
      simpa only [map_add (f := _)] using this
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add f f' _ _ h h' => exact Subalgebra.add_mem _ h h'
  | mul f f' _ _ h h' => exact Subalgebra.mul_mem _ h h'

end PositivityTheory.HtPt.Rh
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenerationAlongInvariants

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem genAF_of_map_eq_invFun : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K :=
  PositivityTheory.HtPt.Rh.sub_pull

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenerationAlongInvariantsStatement

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.generation_along_invariants : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun | exact GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsIsogenyHopfOrder

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∃ (jN : N →+ N') (ψ : T'.A →ₐ[R] T.A), (∀ x, pt' (jN x) = pt x ≫ j) ∧ spMap ψ ≫ T'.y = T.y ≫ j ∧ ∀ g ∈ torsFun C T' pt', (fun x => g (jN x)) ∈ torsFun C T pt := by
  intro p _ C _ _ _ v R _ _ _ _ G _ _ G' _ _ T N _ _ _ pt hpt T' N' _ _ _ pt' hpt' j hj
  haveI := hj
  have hex : ∀ x : N, ∃ y : N', pt' y = pt x ≫ j := by
    intro x
    apply (hpt'.range _).1
    have hx : (pt x) ^ p = 1 := (hpt.range _).2 ⟨x, rfl⟩
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  choose f hf using hex
  have hadd : ∀ x y : N, f (x + y) = f x + f y := by
    intro x y
    apply hpt'.inj
    rw [hpt'.add, hf, hf, hf, hpt.add, MonObj.mul_comp]
  let jN : N →+ N' :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        simpa using h.symm
      map_add' := hadd }
  have hyp : (T.y ≫ j) ^ p = 1 := by
    rw [← MonObj.pow_comp, T.y_p, MonObj.one_comp]
  obtain ⟨ψ, hψ, -⟩ := T'.univ T.A (T.y ≫ j) hyp
  refine ⟨jN, ψ, fun x => hf x, hψ, ?_⟩
  intro g hg
  obtain ⟨a, ha⟩ := hg
  refine ⟨ψ a, ?_⟩
  intro x φ hφ
  have key : spMap (φ.comp ψ) ≫ T'.y = pt' (jN x) := by
    rw [← Chart.spMap_comp ψ φ]
    change (spMap φ ≫ spMap ψ) ≫ T'.y = pt' (f x)
    rw [Category.assoc, hψ, ← Category.assoc, hφ, hf]
  exact ha (jN x) (φ.comp ψ) key
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsIsogenyHopfOrderStatement

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsion_points_isogeny_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∃ (jN : N →+ N') (ψ : T'.A →ₐ[R] T.A), (∀ x, pt' (jN x) = pt x ≫ j) ∧ spMap ψ ≫ T'.y = T.y ≫ j ∧ ∀ g ∈ torsFun C T' pt', (fun x => g (jN x)) ∈ torsFun C T pt := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order | exact GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionAugmentation

section

@[expose] public section

noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem one_comp_monHom {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    [IsMonHom f] : (1 : T ⟶ G) ≫ f = 1 := by
  simp [Hom.one_def]

theorem sub_abelianScheme : QuotientByFiniteFlatStatement → ZarhinStatement →
    HodgeTateDatumStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R →
    v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R →
    ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A →
    L.IsLB → Out.RelAmple A L → ∀ (T : TorsRep A p) (N : Type) [AddCommGroup N] [Fintype N]
    [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ A)), IsTorsPts A p pt →
    ∀ K : AddSubgroup N, GenAF p (torsFun C T pt) K := by
  intro hQ hZ hD p _ C _ _ _ v R _ _ hint hp hc A _ L hA hL hamp T N _ _ _ pt hpt K
  haveI : IsCommMonObj A := hA.comm
  have hsub := GlobalTheory.T.torsion_points_finite_flat_subgroup p C v R hint hp A T N pt hpt K
  obtain ⟨A', _, L', q, hA', hL', hamp', hq, -, -, -, hker⟩ := hQ R A L hA hL hamp _ _ hsub
  obtain ⟨P, i, r, hi, hr, hir⟩ := hZ C v R hint A' L' hA' hL' hamp'
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI := hq
  haveI := hi
  haveI := hr
  have hj : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
      z ≫ (q ≫ i) = 1 ↔ ∃ φ : (T.A ⧸ vanIdeal T pt K) →ₐ[R] S,
        spMap φ ≫ (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) = z := by
    intro S _ _ z
    rw [← hker S z]
    constructor
    · intro h
      have h1 : (z ≫ q ≫ i) ≫ r = z ≫ q := by simp [hir]
      rw [← h1, h, one_comp_monHom]
    · intro h
      rw [← Category.assoc, h, one_comp_monHom]
  letI : Algebra ℤ_[p] R := (Av.zpLift p R hc).toAlgebra
  obtain ⟨⟨T'⟩, cp, -, -, pt', hpt', -⟩ := hD p C v R hint hp hc P
  have hjm : IsMonHom (q ≫ i) := inferInstance
  obtain ⟨jN, -, hjN, -, hpull⟩ := GlobalTheory.T.torsion_points_isogeny_hopf_order p C v R hint hp A P.A T N pt hpt T' _ pt' hpt'
    (q ≫ i) hjm
  obtain ⟨hK, hid⟩ := GlobalTheory.T.torsion_points_homomorphism_compatible p C v R hint hp A P.A T N pt hpt T' _ pt' hpt' (q ≫ i) hjm K
    hj jN hjN
  obtain ⟨⟨AA, hAA⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hint hp A T N pt hpt
  obtain ⟨⟨AP, hAP⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hint hp P.A T' _ pt' hpt'
  have hinv := GlobalTheory.T.hopf_order_pullback_along_hom p C v R hint hp N AA _ AP jN
    (by rw [hAA, hAP]; exact hpull) (by rw [hAA, hAP]; exact hid)
  rw [hAA, hAP, hK] at hinv
  exact GlobalTheory.T.generation_along_invariants p C R N _ _ _ jN K hinv (gp_polAV hD p C v R hint hp hc P T' _ pt' hpt').1

end GlobalTheory.CompanionTheory.Ar.GR
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionAugmentationStatement

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_scheme_torsion_augmentation : QuotientByFiniteFlatStatement → ZarhinStatement → HodgeTateDatumStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → ∀ (T : TorsRep A p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ A)), IsTorsPts A p pt → ∀ K : AddSubgroup N, GenAF p (torsFun C T pt) K := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.sub_abelianScheme | exact GlobalTheory.CompanionTheory.Ar.GR.sub_abelianScheme | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.sub_abelianScheme <;> assumption)
end
end
