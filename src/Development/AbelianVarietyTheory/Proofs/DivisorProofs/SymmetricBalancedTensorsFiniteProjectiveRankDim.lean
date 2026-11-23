module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedSymmetricLieTensorsFiniteProjectiveRankStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenRankInteriorEqSignatureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenEigenRankLevelSetIntegersActionStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSignatureSumEqTwiceDimension

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalProj

theorem signature_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ),
    ∑ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) *
      (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) =
      2 * (Module.finrank ℚ E / 2 * p * q) := by
  intro E _ _ _ H p q
  have hdpos : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 := H.sqrt_neg_disc_sq
  have hre : H.rt0.re = 0 := by
    have e1 := congrArg Complex.re h0
    have e2 := congrArg Complex.im h0
    have e3 : H.rt0.re * H.rt0.im = 0 := by
      simp only [pow_two, Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at e2
      linarith
    simp only [pow_two, Complex.mul_re, Complex.neg_re, Complex.natCast_re] at e1
    rcases mul_eq_zero.mp e3 with h | h
    · exact h
    · exfalso
      rw [h] at e1
      nlinarith [sq_nonneg H.rt0.re]
  have hne : H.rt0 ≠ 0 := by
    intro h
    rw [h] at h0
    have : (H.d : ℂ) = 0 := by simpa using h0
    exact hdpos.ne' (by exact_mod_cast this)
  have hconj : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hnn : H.rt0 ≠ -H.rt0 := by
    intro h
    apply hne
    have : (2 : ℂ) * H.rt0 = 0 := by rw [two_mul]; nth_rewrite 2 [h]; ring
    simpa using this
  have key : ∀ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) *
      (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) = p * q := by
    intro τ
    have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      have hrtE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
        have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
        simpa using this
      rw [← map_pow, hrtE, h0]
      simp
    have hor : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rcases hor with h | h
    · rw [if_pos h, h, hconj, if_neg (Ne.symm hnn)]
    · rw [if_neg (by rw [h]; exact Ne.symm hnn), h, map_neg, hconj, neg_neg, if_pos rfl, mul_comm]
  rw [Finset.sum_congr rfl (fun τ _ => key τ), Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card E ℂ, smul_eq_mul, NumberField.IsTotallyComplex.finrank]
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  ring

end GlobalTheory.BalProj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSignatureSumEqTwiceDimensionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cmType_signature_sum_eq_twice_dimension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ), ∑ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) * (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) = 2 * (Module.finrank ℚ E / 2 * p * q) := by
  first | exact @GlobalTheory.BalProj.signature_count | exact GlobalTheory.BalProj.signature_count | (intros; apply GlobalTheory.BalProj.signature_count <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseAffineChartPreimageInterior

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalProj

theorem chart_dense_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens), Dense ((chart U).base ⁻¹' (interior Y : Set Y.X)) := by
  intro E _ _ _ H Dw l Xo c Y U
  have hi := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have h : IsOpenMap (chart U).base := (Scheme.Hom.isOpenEmbedding (f := U.2.fromSpec)).isOpenMap
  exact (dense_interior Y).preimage h

end GlobalTheory.BalProj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseAffineChartPreimageInteriorStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dense_affineChart_preimage_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens), Dense ((chart U).base ⁻¹' (interior Y : Set Y.X)) := by
  first | exact @GlobalTheory.BalProj.chart_dense_interior | exact GlobalTheory.BalProj.chart_dense_interior | (intros; apply GlobalTheory.BalProj.chart_dense_interior <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionMatricesRingHom

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BalProj

theorem actMat_ringHom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Scheme.{0}} (t : SAB H X) (S : Type) [CommRing S] (x0 : Spec (CommRingCat.of S) ⟶ X) (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) S), (∀ i, IsTanAtG t x0 (v i)) → (∀ w, IsTanAtG t x0 w → ∃! cf : Fin n → S, IsCombAtG t x0 v cf w) → (∀ a i, IsCombAtG t x0 v (A a i) (v i ≫ (t.act.act a).left)) → A 1 = 1 ∧ (∀ a b, A (a + b) = A a + A b) ∧ (∀ a b, A (a * b) = A a * A b) := by
  intro E _ _ _ H X t S _ x0 n v A hv hb hA
  classical
  let T : Fin n → TanM x0 t.G := fun i => GlobalTheory.LieMet.tanOf (hv i)
  have uniq : ∀ c c' : Fin n → S, ∑ j, c j • T j = ∑ j, c' j • T j → c = c' := by
    intro c c' h
    obtain ⟨cf, _, hcf⟩ := hb _ (GlobalTheory.LieMet.isTan_tv (∑ j, c j • T j))
    have h1 : IsCombAtG t x0 v c (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c _).2 rfl
    have h2 : IsCombAtG t x0 v c' (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c' _).2 h
    exact (hcf _ h1).trans (hcf _ h2).symm
  have hact : ∀ a i, ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i) = ∑ j, A a i j • T j := fun a i =>
    (GlobalTheory.LieMet.isComb_iff T (A a i) (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i))).1 (hA a i)
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have e : ∑ k, A 1 i k • T k = ∑ k, (1 : Matrix (Fin n) (Fin n) S) i k • T k := by
      rw [← hact, map_one, Module.End.one_apply]
      simp [Matrix.one_apply]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a + b) i k • T k = ∑ k, (A a + A b) i k • T k := by
      rw [← hact, map_add (f := _), LinearMap.add_apply, hact, hact]
      simp [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a * b) i k • T k = ∑ k, (A a * A b) i k • T k := by

      rw [← hact, mul_comm a b, map_mul, Module.End.mul_apply, hact, map_sum]
      simp only [map_smul, hact, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      exact Finset.sum_comm
    exact congrFun (uniq _ _ e) j

end GlobalTheory.BalProj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionMatricesRingHomStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tangentBasis_actionMatrices_ringHom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Scheme.{0}} (t : SAB H X) (S : Type) [CommRing S] (x0 : Spec (CommRingCat.of S) ⟶ X) (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) S), (∀ i, IsTanAtG t x0 (v i)) → (∀ w, IsTanAtG t x0 w → ∃! cf : Fin n → S, IsCombAtG t x0 v cf w) → (∀ a i, IsCombAtG t x0 v (A a i) (v i ≫ (t.act.act a).left)) → A 1 = 1 ∧ (∀ a b, A (a + b) = A a + A b) ∧ (∀ a b, A (a * b) = A a * A b) := by
  first | exact @GlobalTheory.BalProj.actMat_ringHom | exact GlobalTheory.BalProj.actMat_ringHom | (intros; apply GlobalTheory.BalProj.actMat_ringHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBalancedTensorsFiniteProjectiveRankDim

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BalProj

theorem balanced_finite_projective_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA
  obtain ⟨h1A, haddA, hmulA⟩ := GlobalTheory.T.tangentBasis_actionMatrices_ringHom H Y.t Γ(Y.X, U.1) (chart U) n v A hv hb hA
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.balancedSymmetricLieTensors_finite_projective_rank H c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA
  refine ⟨hfin, hproj, fun m hm => ?_⟩
  have key : ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) m.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
    intro τ
    set e : ℕ := if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q with he
    let f : PrimeSpectrum Γ(Y.X, U.1) → ℕ := fun 𝔭 => GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ)
    have hop : ∀ N, IsOpen {𝔭 | f 𝔭 = N} := fun N =>
      GlobalTheory.T.isOpen_eigenRank_levelSet_integersAction c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA τ N
    have hcl : IsClosed {𝔭 | f 𝔭 = e} := by
      rw [← isOpen_compl_iff]
      have : {𝔭 | f 𝔭 = e}ᶜ = ⋃ N ∈ {N : ℕ | N ≠ e}, {𝔭 | f 𝔭 = N} := by
        ext 𝔭; simp
      rw [this]
      exact isOpen_biUnion fun N _ => hop N
    have hsub : (chart U).base ⁻¹' (interior Y : Set Y.X) ⊆ {𝔭 | f 𝔭 = e} := fun 𝔭 h𝔭 =>
      GlobalTheory.T.eigenRank_interior_eq_signature E H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA 𝔭 h𝔭 τ
    have hall : {𝔭 | f 𝔭 = e} = Set.univ :=
      Set.eq_univ_of_univ_subset ((GlobalTheory.T.dense_affineChart_preimage_interior E H Dw l Xo c Y U).closure_eq ▸ (closure_mono hsub).trans hcl.closure_subset)
    have := hall ▸ Set.mem_univ (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(Y.X, U.1))
    exact this
  have h2 := hrk m
  simp_rw [key] at h2
  rw [GlobalTheory.T.cmType_signature_sum_eq_twice_dimension E H Dw.p Dw.q] at h2
  unfold Datum.dim
  omega

end GlobalTheory.BalProj
end
end
