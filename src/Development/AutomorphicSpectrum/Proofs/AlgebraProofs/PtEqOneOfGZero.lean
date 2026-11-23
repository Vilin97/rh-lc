module

public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNilpotentGroupChartSmoothCommGroup
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesReadingGroupHomNilpotentCharts
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HopfPointMem
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionRepresentationStatement
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupChartFamily
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import ReciprocityTheory.DualLattices.CotangentSurjective
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedVarietyIntegerActionStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialPolarizedAbelianPointEqOneStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.DualLattices.IsLocalOfIntegers

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupChartFamilyStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

theorem _root_.GlobalTheory.T.formal_group_chart_family : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (P : Out.PolAV (Geo.Tor.Sp O)), 1 ≤ P.g → ∀ (g : ℕ), P.g = g → ∀ (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE) (F : FGLaw O g) (X : Fam P.A g), NilChart P.A F.F X → ∀ α : OE → Fin g → PS O 1 g, (∀ a, Reads X X (o.act a) (α a)) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O) (pt : Nb p g → (sp (R₀ := O) O ⟶ P.A)), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ (∀ i, ∃ u : PS O 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧ IsTorsPts P.A p pt ∧ (∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt) ∧ ∀ (a : OE) (t : TT p g), pt (red p g (H.ρ (1 ⊗ₜ[ℤ] a) *ᵥ t)) = pt (red p g t) ≫ o.act a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.exists_htd_act | exact GlobalTheory.CompanionTheory.Ar.GR.exists_htd_act | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.exists_htd_act <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateDatumReduceScalars

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem htd_restrict_coefficients : ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : R), HodgeTateSetting p v R Oe σ cp → ∀ H : HodgeTateDatum p g v R Oe σ cp, HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp ∧ ∃ H' : HodgeTateDatum p g v R ℤ_[p] AlgEquiv.refl cp, H'.AA = H.AA ∧ H'.Ht = H.Ht ∧ H'.Bt = H.Bt ∧ H'.E = H.E := by
  intro p _ g C _ v R _ _ _ Oe _ _ σ cp hS H
  refine ⟨⟨hS.integers, hS.p_lt, hS.p_ne, hS.cp_val, fun _ => rfl⟩,
    { ρ := H.ρ.comp (Algebra.ofId _ _)
      ρL := H.ρL.comp (algebraMap _ _)
      P := H.P
      PL := H.PL
      E := H.E
      E_alternating := H.E_alternating
      isUnit_det_E := H.isUnit_det_E
      E_equivariant := fun a => ?_
      projectors := ⟨H.projectors.1, H.projectors.2.1, H.projectors.2.2.1, fun a => H.projectors.2.2.2.1 _, fun a => H.projectors.2.2.2.2 _⟩
      Ht := H.Ht
      Bt := H.Bt
      Ht_equivariant := ⟨fun a => ?_, H.Ht_equivariant.2⟩
      form_eq_alt := H.form_eq_alt
      AA := H.AA
      h3 := fun a => H.h3 _
      h4 := H.h4
      h5 := H.h5
      φ := H.φ
      cotangent_surjective := H.cotangent_surjective
      cotangent_ker_eq := H.cotangent_ker_eq
      cotangent_linear := fun a => H.cotangent_linear _ }, rfl, rfl, rfl, rfl⟩
  · have := H.E_equivariant (algebraMap ℤ_[p] Oe a)
    rw [σ.commutes] at this
    exact this
  · have := H.Ht_equivariant.1 (algebraMap ℤ_[p] Oe a)
    rw [σ.commutes] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.GR
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateDatumReduceScalarsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

theorem _root_.GlobalTheory.T.hodge_tate_datum_reduce_scalars : ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : R), HodgeTateSetting p v R Oe σ cp → ∀ H : HodgeTateDatum p g v R Oe σ cp, HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp ∧ ∃ H' : HodgeTateDatum p g v R ℤ_[p] AlgEquiv.refl cp, H'.AA = H.AA ∧ H'.Ht = H.Ht ∧ H'.Bt = H.Bt ∧ H'.E = H.E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.htd_restrict_coefficients | exact GlobalTheory.CompanionTheory.Ar.GR.htd_restrict_coefficients | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.htd_restrict_coefficients <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtEqOneOfGZero

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

namespace GlobalTheory.CompanionTheory.Ar.GR.Top

theorem pt_eq_one_of_g_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))), P.g = 0 → ∀ z : sp (R₀ := R) R ⟶ P.A, z = 1 :=
  GlobalTheory.T.trivial_polarized_abelian_point_eq_one

theorem exists_cp (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] (hv : v.Integers R)
    (hpv : v (p : C) < 1) :
    ∃ cp : R, v (algebraMap R C cp) ^ (p - 1) = v (algebraMap R C (p : R)) := by
  have h1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (p : C) h1
  have hle : v c ≤ 1 := by
    by_contra h
    push_neg at h
    have : 1 < v c ^ (p - 1) := one_lt_pow₀ h h1.ne'
    rw [← map_pow, hc] at this
    exact absurd hpv (not_lt.2 this.le)
  obtain ⟨r, hr⟩ := hv.exists_of_le_one hle
  exact ⟨r, by rw [hr, ← v.map_pow, hc, map_natCast (algebraMap R C)]⟩

theorem hopf_carrier_g_zero {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {R : Type} [CommRing R]
    [Algebra R C] (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) R (Nb p 0)) :
    AA.carrier = ReciprocityTheory.PGsh.L2.intFun R (Nb p 0) := by
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  refine le_antisymm AA.le_int fun f hf => ?_
  obtain ⟨r, hr⟩ := hf default
  have : f = r • (1 : Nb p 0 → C) := by
    funext x
    rw [Subsingleton.elim x default, ← hr]
    simp [Algebra.smul_def]
  rw [this]
  exact AA.carrier.smul_mem r AA.one_mem

theorem torsFun_one_eq {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {R : Type} [CommRing R]
    [Algebra R C] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (T : TorsRep G p) :
    torsFun C T (fun _ : Nb p 0 => (1 : sp (R₀ := R) R ⟶ G)) = ReciprocityTheory.PGsh.L2.intFun R (Nb p 0) := by
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  obtain ⟨φ₀, hφ₀, -⟩ := T.univ R (1 : sp (R₀ := R) R ⟶ G) (one_pow p)
  ext f
  constructor
  · rintro ⟨a, ha⟩ x
    exact ⟨φ₀ a, (ha x φ₀ hφ₀).symm⟩
  · intro hf
    obtain ⟨r, hr⟩ := hf default
    refine ⟨algebraMap R T.A r, fun x φ _ => ?_⟩
    rw [Subsingleton.elim x default, ← hr, AlgHom.commutes]
    rfl

theorem main : HodgeTateDatumStatement := by
  intro p _ C _ _ _ v R _ _ hv hp hcomp _ P
  haveI : IsLocalRing R := isLocal_of_integers hv
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI : Fact ¬IsUnit (p : R) := ⟨fun hu => by
    have h1 := hv.one_of_isUnit hu
    rw [map_natCast] at h1
    rw [h1] at hp
    exact lt_irrefl _ hp⟩
  haveI : IsAdicComplete (Ideal.span {(p : R)}) R := hcomp
  haveI : IsCommMonObj P.A := P.isAb.comm
  have hT : Nonempty (TorsRep P.A p) :=
    GlobalTheory.T.abelian_scheme_torsion_representation R p (Fact.out : p.Prime).one_le P.A P.L P.isAb P.isLB P.ample
  refine ⟨hT, ?_⟩
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · obtain ⟨cp, hcp⟩ := exists_cp p hv hp
    have hpne : v (algebraMap R C (p : R)) ≠ 0 := by
      rw [map_natCast]
      exact fun h => Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero ((Valuation.zero_iff v).1 h)
    have hplt : v (algebraMap R C (p : R)) < 1 := by rwa [map_natCast]
    have hS : HodgeTateSetting p v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp := by
      refine ⟨hv, hplt, hpne, hcp, ?_⟩
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        have h : ∀ (x : ℤ_[p]) (y : ℤ), sigE p ℤ (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ℤ] star y := fun _ _ => rfl
        rw [h, h, star_star]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    obtain ⟨H⟩ := GlobalTheory.ChF.htd_dim_zero p C v R hv ℤ cp
    rw [← hg] at H
    obtain ⟨hS', H', -⟩ := GlobalTheory.T.hodge_tate_datum_reduce_scalars p P.g C v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp hS H
    have h1 := pt_eq_one_of_g_zero R P hg
    revert H'
    rw [hg]
    intro H'
    refine ⟨cp, hS', H', fun _ => 1, ⟨?_, ?_, ?_⟩, fun T => ?_⟩
    · intro x y _
      let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
      exact Subsingleton.elim x y
    · intro x y
      exact (_root_.mul_one _).symm
    · intro z
      exact ⟨fun _ => ⟨0, (h1 z).symm⟩, fun _ => by rw [h1 z]; exact one_pow p⟩
    · rw [hopf_carrier_g_zero, torsFun_one_eq]
  · obtain ⟨F, X, hX⟩ := GlobalTheory.ChF.exists_nilChart R P.A P.g P.smoothDim
    obtain ⟨o⟩ := GlobalTheory.T.polarised_variety_integer_action R P
    have hα : ∀ a : ℤ, ∃ φ, Reads X X (o.act a) φ := fun a =>
      GlobalTheory.ChF.exists_reads R P.A P.A _ _ F.F F.F X X hX hX (o.act a) (o.hom a)
    choose α hα using hα
    obtain ⟨cp, hS, H, S, pt, -, -, -, -, -, hpt, hAA, -⟩ :=
      GlobalTheory.T.formal_group_chart_family p C v R hv P hg P.g rfl ℤ o F X hX α hα
    obtain ⟨hS', H', hAA', -⟩ := GlobalTheory.T.hodge_tate_datum_reduce_scalars p P.g C v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp hS H
    exact ⟨cp, hS', H', pt, hpt, fun T => by rw [hAA']; exact hAA T⟩

end GlobalTheory.CompanionTheory.Ar.GR.Top
end
end
