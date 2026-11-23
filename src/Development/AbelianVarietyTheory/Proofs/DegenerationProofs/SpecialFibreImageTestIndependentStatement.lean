module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegreeFormsDimensionGenericFibreLe
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValHomEq
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinrankSpanReductionLe
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LePreimageOpenPartIffTestCoordinatesStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Mathlib.RingTheory.Nullstellensatz
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomogenisation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormVanishesOfTorsionTorusExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByWeightZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VanishingIdealConePrimeHomogeneous
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsSpecialFibreSupportCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibreStatement
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegreeFormsDimensionGenericFibreLeStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.degreeFormsDimension_genericFibre_le : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (J : Type) [Fintype J] (σ : J → (u.H S.N).Sec) (d : ℕ), 1 ≤ d → hilb {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w} d ≤ (S.N * d) ^ S.g := by
  first | exact @GlobalTheory.ZH.FormCount.hilb_generic_le | exact GlobalTheory.ZH.FormCount.hilb_generic_le | (intros; apply GlobalTheory.ZH.FormCount.hilb_generic_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VanishingIdealConePrimeHomogeneousStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.vanishing_ideal_cone_prime_homogeneous : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) [Fintype J] (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → IsIntegral X → ∀ g : ℕ, SmoothOfRelativeDimension g p → (MvPolynomial.vanishingIdeal k (cone p H s)).IsPrime ∧ (MvPolynomial.vanishingIdeal k (cone p H s)).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) ∧ (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k (cone p H s)) ∧ ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k (cone p H s)) = (g + 1 : ℕ)) := by
  first | exact @GlobalTheory.ZH.ConePrime.isPrime_vanishingIdeal_cone | exact GlobalTheory.ZH.ConePrime.isPrime_vanishingIdeal_cone | (intros; apply GlobalTheory.ZH.ConePrime.isPrime_vanishingIdeal_cone <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemTorusExtensionConeIffSmallDegreeForms

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.FibCone

theorem hilb_eq_finrank_quotPiece {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (quotPiece (MvPolynomial.vanishingIdeal k C) (d : ℤ)) := by
  rw [quotPiece_natCast]
  let ev : MvPolynomial J k →ₐ[k] (C → k) :=
    AlgHom.pi fun v : C => MvPolynomial.aeval v.1
  have hker : ∀ a ∈ MvPolynomial.vanishingIdeal k C, ev a = 0 := fun a ha =>
    funext fun v => ha v.1 v.2
  let φ := Ideal.Quotient.liftₐ (MvPolynomial.vanishingIdeal k C) ev hker
  have hφ : Function.Injective φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 fun v hv => congrFun (show ev x = 0 from hx) ⟨v, hv⟩
  rw [(Submodule.equivMapOfInjective _ hφ _).finrank_eq, ← Submodule.map_comp]
  rfl

theorem eval_eq_zero_of_hilb_le : (∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J] (C : Set (J → k)) (g N : ℕ), (MvPolynomial.vanishingIdeal k C).IsPrime → (MvPolynomial.vanishingIdeal k C).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) → (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k C) → ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k C) = (g + 1 : ℕ) → (∀ d, 1 ≤ d → hilb C d ≤ (N * d) ^ g) → ∀ v : J → k, (∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → Pf ∈ MvPolynomial.vanishingIdeal k C → MvPolynomial.eval v Pf = 0) → ∀ Pf ∈ MvPolynomial.vanishingIdeal k C, MvPolynomial.eval v Pf = 0) := by
  intro k _ _ J _ C g N hP hPh hne hdim hb v hv Pf hPf
  by_contra h0
  obtain ⟨d, hd, f, hf, hfd, hfv⟩ :=
    exists_form_degree_le_hilbertDegree_eval_ne_zero hPh hne v ⟨Pf, hPf, h0⟩
  refine hfv (hv d f (hd.trans ?_) hfd hf)
  have hH := isHilbertPoly_idealHilbertPoly hPh
  have hg : (idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).natDegree = g := by
    rw [ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hPh hne] at hdim
    have := Nat.cast_injective hdim
    omega
  have h1 : 0 ≤ (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g -
      idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).coeff g := by
    apply coeff_nonneg_of_eventually_eval_nat
    · refine (Polynomial.degree_sub_le _ _).trans (max_le (Polynomial.degree_C_mul_X_pow_le _ _) ?_)
      exact Polynomial.degree_le_of_natDegree_le hg.le
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually hH.eventually_eq,
        Filter.eventually_ge_atTop 1] with n hn h1n
      have := hb n h1n
      rw [hilb_eq_finrank_quotPiece, mul_pow] at this
      rw [Int.cast_natCast] at hn
      rw [Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
        ← hn, sub_nonneg]
      exact_mod_cast this
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, _root_.mul_one,
    sub_nonneg] at h1
  have h2 := cast_hilbertDegree hPh
  rw [Polynomial.leadingCoeff, hg] at h2
  have h3 : (hilbertDegree (MvPolynomial.vanishingIdeal k C) : ℚ) ≤ (N : ℚ) ^ g * g.factorial := by
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
  exact_mod_cast h3

theorem isIntegral_G {k : Type} [Field k] (Φ : FibPre k) : IsIntegral Φ.G.left := by
  have h : IsSemiAbelian Φ.G := GlobalTheory.isSemiAbelian_of_isGt _ Φ.E Φ.G ⟨Φ.D⟩
  have := h.smooth
  have := h.geomConnected
  have : GeometricallyIntegral Φ.G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ Φ.G
  exact GeometricallyIntegral.isIntegral_of_subsingleton Φ.G.hom

theorem exists_ne_zero_of_mem_cone {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type}
    (s : J → H.Sec) (J₀ : Set J) (hH : H.IsLB) (hc : ⨆ i ∈ J₀, Out.nonzeroLocus (s i) = ⊤) (v : J → k)
    (hv : v ∈ cone p H s) : ∃ i ∈ J₀, v i ≠ 0 := by
  obtain ⟨x, -, hx⟩ := hv
  let pt : Sp k := IsLocalRing.closedPoint k
  have hm : x pt ∈ (⨆ i ∈ J₀, Out.nonzeroLocus (s i)) := by rw [hc]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, hi, hm⟩ := hm
  refine ⟨i, hi, ?_⟩
  have hu := (((GlobalTheory.ZH.CrdCalc.crd_calculus X H J s hH).1 k x).2.2 v i hx).2 (by
    intro y _
    have : y = pt := Subsingleton.elim (α := PrimeSpectrum k) _ _
    subst this
    exact hm)
  exact hu.ne_zero

theorem mem_cone_iff : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → SmoothOfRelativeDimension g Φ.G.hom → (∀ d, 1 ≤ d → hilb (cone Φ.G.hom (Φ.H 1) F) d ≤ (N * d) ^ g) → ∀ v : J → k, v ∈ cone Φ.G.hom (Φ.H 1) F ↔ ((∃ i, cls i = 0 ∧ v i ≠ 0) ∧ ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ w, Crd (Φ.H 1) F x.left w ∧ MvPolynomial.eval w Pf = 0) → MvPolynomial.eval v Pf = 0)) := by
  intro hL hL2 k _ _ Φ g N N' q J _ cls F π hB hG hg hN hsm hh v
  have hH := Φ.H_isLB 1
  have himm := GlobalTheory.T.immBy_weight_zero' hL hL2 k Φ g N N' q J cls F π hB hG hg
  constructor
  · intro hv
    exact ⟨exists_ne_zero_of_mem_cone _ _ F _ hH himm.1 v hv, fun d Pf hd hP ht =>
      GlobalTheory.T.form_vanishes_of_torsion_torusExtension hL hL2 k Φ g N N' q J cls F π hB hG hg hN d Pf hd hP ht v hv⟩
  · rintro ⟨h0, hv⟩
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.vanishing_ideal_cone_prime_homogeneous k _ Φ.G.hom (Φ.H 1) J F _ hH himm (isIntegral_G Φ) g hsm
    refine GlobalTheory.ZH.ConeClosed.mem_cone_of_vanishing k _ Φ.G.hom (Φ.H 1) J F _ hH himm v h0 ?_
    refine eval_eq_zero_of_hilb_le k J _ g N h1 h2 h3 h4 hh v fun d Pf hd hP hI => hv d Pf hd hP ?_
    intro x _
    obtain ⟨w, hw⟩ := ((GlobalTheory.ZH.CrdCalc.crd_calculus _ (Φ.H 1) J F hH).1 k x.left).1
    refine ⟨w, hw, ?_⟩
    have := (MvPolynomial.mem_vanishingIdeal_iff.1 hI) w ⟨x.left, Over.w x, hw⟩
    simpa [MvPolynomial.aeval_eq_eval] using this

end GlobalTheory.ZH.FibCone
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemTorusExtensionConeIffSmallDegreeFormsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.mem_torusExtensionCone_iff_smallDegreeForms : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → SmoothOfRelativeDimension g Φ.G.hom → (∀ d, 1 ≤ d → hilb (cone Φ.G.hom (Φ.H 1) F) d ≤ (N * d) ^ g) → ∀ v : J → k, v ∈ cone Φ.G.hom (Φ.H 1) F ↔ ((∃ i, cls i = 0 ∧ v i ≠ 0) ∧ ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ w, Crd (Φ.H 1) F x.left w ∧ MvPolynomial.eval w Pf = 0) → MvPolynomial.eval v Pf = 0)) := by
  first | exact @GlobalTheory.ZH.FibCone.mem_cone_iff | exact GlobalTheory.ZH.FibCone.mem_cone_iff | (intros; apply GlobalTheory.ZH.FibCone.mem_cone_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreImageTestIndependent

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TestFib

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} {p : ℕ} [Fact p.Prime]

theorem level_ne_zero (S : ThetaSys o Ω) (y : Sp (OO p) ⟶ M.Z) : ((S.r * S.N : ℕ) : kb p) ≠ 0 := by
  have h := S.unit.map (Spec.preimage (rPt p ≫ y ≫ M.s)).hom
  rw [map_natCast] at h
  exact h.ne_zero

variable {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u}

abbrev mb (tm : Q.TMap t c) : Matrix S.J S.J (kb p) :=
  tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)

theorem isUnit_det_mb (tm : Q.TMap t c) : IsUnit (mb tm).det := by
  have h := tm.unit.map ((IsLocalRing.residue (OO p)).comp t.u.j)
  rw [RingHom.map_det] at h
  exact h

theorem crd_image (tm : Q.TMap t c) (x₀ : Sp (kb p) ⟶ t.mod.Φ.G.left) (hx : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _)
    (v : S.J → kb p) (hv : Crd (t.mod.Φ.H 1) t.mod.F x₀ v) :
    (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧
      Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) ((x₀ ≫ t.mod.r) ≫ tm.f) ((mb tm).mulVec v) := by
  have h1 : (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j := by
    rw [Category.assoc, t.mod.cart.1.w, ← Category.assoc, hx]
    exact Category.id_comp _
  refine ⟨h1, tm.crd (kb p) ((IsLocalRing.residue (OO p)).comp t.u.j) _ v (h1.trans ?_)
    (t.mod.red (Over.homMk x₀ hx) v hv)⟩
  exact (Spec.map_comp _ _).symm

theorem image_over (tm : Q.TMap t c) (c' : Sp (kb p) ⟶ t.u.G.left) (h : c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j) :
    (c' ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
  rw [Category.assoc, tm.f_over, ← Category.assoc, h, Category.assoc, c.fac]

theorem mem_cone_iff [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hB : BaseFacts S M U₀ EE) (tm : Q.TMap t c) (hS : S.Big)
    (v : S.J → kb p) :
    v ∈ cone t.mod.Φ.G.hom (t.mod.Φ.H 1) t.mod.F ↔ (∃ i, t.cls i = 0 ∧ v i ≠ 0) ∧
      ∀ (d : ℕ) (Pf : MvPolynomial S.J (kb p)), d ≤ S.N ^ S.g * S.g.factorial → Pf.IsHomogeneous d →
        (∀ w ∈ Q.Tors (rPt p ≫ y) tm.l, MvPolynomial.eval w Pf = 0) →
        MvPolynomial.eval ((mb tm).mulVec v) Pf = 0 := by
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hsm : SmoothOfRelativeDimension S.g t.mod.Φ.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback t.mod.cart.1 t.mod.smooth
  have hbig : Big S.g S.N (S.r * S.N) := ⟨(GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ t.u).2.2.2.1, hS.1, hS.2.1⟩
  have key := GlobalTheory.T.mem_torusExtensionCone_iff_smallDegreeForms hL.1 hL.2.1 (kb p) t.mod.Φ S.g S.N (S.r * S.N) _ S.J _ t.mod.F t.mod.pol hbig
    t.mod.good t.mod.dim (level_ne_zero S y) hsm
    (fun d hd => (Mod.hilb_special_le_generic p _ _ _ _ _ 0 _ _ _ _ _ _ t.mod d).trans
      (GlobalTheory.T.degreeFormsDimension_genericFibre_le hL o Ω S ρ p y₀ t.u S.J t.σ d hd)) v
  obtain ⟨T₁, T₂⟩ := GlobalTheory.T.torsionPoints_specialFibre_supportCoordinates hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS
  have hinv : ∀ w, (mb tm)⁻¹.mulVec ((mb tm).mulVec w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_mb tm), Matrix.one_mulVec]
  refine key.trans (and_congr (exists_congr fun i => and_congr (map_eq_zero_iff _ t.mod.xe.symm.injective) Iff.rfl)
    ⟨fun H d Pf hd hPf hT => ?_, fun H d Pf hd hPf hT => ?_⟩)
  · obtain ⟨F, hF, hev⟩ := InFibChart.exists_subst (mb tm) hPf
    rw [← hev]
    refine H d F hd hF fun x hx => ?_
    obtain ⟨w, hw, hw'⟩ := T₁ x hx
    exact ⟨w, hw, (hev w).trans (hT _ hw')⟩
  · obtain ⟨F, hF, hev⟩ := InFibChart.exists_subst (mb tm)⁻¹ hPf
    rw [← hinv v, ← hev]
    refine H d F hd hF fun w hw => ?_
    obtain ⟨x, w₀, hx, hw₀, rfl⟩ := T₂ w hw
    obtain ⟨w₁, hw₁, h0⟩ := hT x hx
    obtain ⟨u, hu⟩ := CrdCalc.crd_unique hw₁ hw₀
    rw [hev, hinv, show w₀ = fun j => (u : kb p) * w₁ j from funext hu, InFibChart.eval_scale _ _ hPf, h0, mul_zero]

theorem image_special_fibre_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ x : Sp (kb p) ⟶ Q.P.left, x ≫ Q.P.hom = rPt p ≫ y → ((∃ c' : Sp (kb p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x) ↔ (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS x hx
  constructor
  · rintro ⟨c', hc', rfl⟩
    let x₀ : Sp (kb p) ⟶ t.mod.Φ.G.left := t.mod.cart.1.lift c' (𝟙 _) (hc'.trans (Category.id_comp _).symm)
    have h₁ : x₀ ≫ t.mod.r = c' := t.mod.cart.1.lift_fst _ _ _
    have h₂ : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _ := t.mod.cart.1.lift_snd _ _ _
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists (t.mod.Φ.H_isLB 1) t.mod.F x₀
    have hcr := (crd_image tm x₀ h₂ v hv).2
    rw [h₁] at hcr
    have hov := image_over tm c' hc'
    obtain ⟨k₁, k₂⟩ := (mem_cone_iff hL hB tm hS v).1 ⟨x₀, h₂, hv⟩
    rw [← Category.assoc]
    refine ⟨(GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS _ v hov hcr).2 k₁,
      InFibChart.inFib_of_chart o Ω S ρ M U₀ EE hB Q _ tm.l _ _ hcr ?_⟩
    rw [hov]
    exact k₂
  · rintro ⟨hG, hF⟩
    obtain ⟨x', rfl⟩ : ∃ x' : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme, x' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x := by
      refine ⟨IsOpenImmersion.lift _ x ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      have e : Q.P.hom (x w) = y (rPt p w) :=
        (Scheme.Hom.comp_apply _ _ _).symm.trans
          ((congrArg (fun f : Sp (kb p) ⟶ M.Z => f w) hx).trans (Scheme.Hom.comp_apply _ _ _))
      show Q.P.hom (x w) ∈ Q.W tm.l
      rw [e]
      exact ((IsLocalRing.specializes_closedPoint (rPt p w)).map y.continuous).mem_open (Q.W tm.l).isOpen tm.mem
    have hLB : (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι).IsLB := LB.isLB_pull Q.isLB _
    obtain ⟨w, hw⟩ := CrdCalc.crd_exists hLB (Q.σ tm.l) x'
    obtain ⟨v, rfl⟩ : ∃ v, (mb tm).mulVec v = w := ⟨(mb tm)⁻¹.mulVec w, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_mb tm), Matrix.one_mulVec]⟩
    have hx' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := (Category.assoc _ _ _).symm.trans hx
    have k₂ := hF tm.l x' _ rfl hw
    rw [hx] at k₂
    obtain ⟨x₀, h₂, hv⟩ := (mem_cone_iff hL hB tm hS v).2
      ⟨(GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS x' v hx' hw).1 hG, k₂⟩
    obtain ⟨h₁, hcr⟩ := crd_image tm x₀ h₂ v hv
    refine ⟨x₀ ≫ t.mod.r, h₁, ?_⟩
    have e : ((x₀ ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ∣_ Q.W tm.l) = x' ≫ (Q.P.hom ∣_ Q.W tm.l) := by
      rw [← cancel_mono (Q.W tm.l).ι, Category.assoc, Category.assoc x', morphismRestrict_ι, hx']
      exact image_over tm _ h₁
    rw [← Category.assoc, ImmSep.eq_of_crd_eq _ _ _ _ _ _ _ hLB (Q.imm tm.l) (kb p) _ x' _
      (by rw [← Category.assoc, e, Category.assoc]) hcr hw]

end GlobalTheory.ZH.TestFib
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreImageTestIndependentStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.specialFibre_image_test_independent : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ x : Sp (kb p) ⟶ Q.P.left, x ≫ Q.P.hom = rPt p ≫ y → ((∃ c' : Sp (kb p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x) ↔ (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  first | exact @GlobalTheory.ZH.TestFib.image_special_fibre_iff | exact GlobalTheory.ZH.TestFib.image_special_fibre_iff | (intros; apply GlobalTheory.ZH.TestFib.image_special_fibre_iff <;> assumption)
end
end
