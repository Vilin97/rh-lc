module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfKillsTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinearStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmplePullbackIntersectionDegreePosOfNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymmStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordClassSymmetricPullbackQuadraticStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeOfPositiveDefiniteFormBoundedRank
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFinrankOfInjectiveModPrimePosDefFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDimStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfTateModuleMapEqSmul

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_nsmul_eq_of_tmap_eq_smul : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (f : A ⟶ B) (φ : Tl l A →ₗ[ℤ_[l]] Tl l B),
      tmap l A B f = (l : ℤ_[l]) • φ → ∃ g : A ⟶ B, f = l • g := by
  intro K _ l _ hl A B f φ hf
  refine exists_nsmul_eq_of_kills_torsion K A B f l hl fun x hx => ?_
  obtain ⟨t, ht⟩ := (tl_lev_surj_ker K l A 1).1 x (by rwa [pow_one])
  have h1 : (tmap l A B f t).lev 1 = x ≫ f.hom := by rw [lev_tmap, ht]
  rw [← h1, hf, LinearMap.smul_apply]
  exact ((tl_lev_surj_ker K l B 1).2 _).2 ⟨φ t, by rw [pow_one]⟩

end GlobalTheory.AV.AbVar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfTateModuleMapEqSmulStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_nsmul_eq_of_tateModuleMap_eq_smul : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B) (φ : Tl l A →ₗ[ℤ_[l]] Tl l B), tmap l A B f = (l : ℤ_[l]) • φ → ∃ g : A ⟶ B, f = l • g := by
  first | (exact @GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul) | (exact GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul) | (intros; apply GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDimEqZero

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.AbVar

theorem isIso_hom_of_dim_eq_zero {K : Type} [Field K] (A : AbVar K) (h : A.dim = 0) : IsIso A.X.hom := by
  have hA := A.ab
  have : IsProper A.X.hom := hA.proper
  have hs : SmoothOfRelativeDimension 0 A.X.hom := h ▸ A.smooth
  have : Etale A.X.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hs
  let e : Sp K ⟶ A.X.left := (1 : 𝟙_ (Over (Sp K)) ⟶ A.X).left
  have he : e ≫ A.X.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over (Sp K)) ⟶ A.X)
  have : IsOpenImmersion e := isOpenImmersion_of_section_of_etale A.X.hom e he
  have : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ A.X.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.X.hom
  obtain ⟨hI, -, -⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  have : ConnectedSpace A.X.left := inferInstance
  have hne : (Set.range e).Nonempty := ⟨_, (default : PrimeSpectrum K), rfl⟩
  have hsurj : Function.Surjective e := Set.range_eq_univ.1
    (IsClopen.eq_univ ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩ hne)
  have : Surjective e := ⟨hsurj⟩
  have : IsIso e := IsOpenImmersion.isIso e
  have : IsIso (e ≫ A.X.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e A.X.hom

theorem hom_eq_of_isIso {K : Type} [Field K] {A : AbVar K} (h : IsIso A.X.hom) {T : Over (Sp K)}
    (g₁ g₂ : T ⟶ A.X) : g₁ = g₂ := by
  ext
  rw [← cancel_mono A.X.hom, Over.w, Over.w]

theorem eq_zero_of_dim_eq_zero :
    ∀ (K : Type) [Field K] (A B : AbVar K), (A.dim = 0 ∨ B.dim = 0) → ∀ f : A ⟶ B, f = 0 := by
  intro K _ A B h f
  rcases h with h | h
  · have hi := isIso_hom_of_dim_eq_zero A h
    apply Subtype.ext
    change f.hom = (0 : A ⟶ B).hom
    rw [zero_hom]
    have e1 : f.hom = (1 : A.X ⟶ A.X) ≫ f.hom := by
      rw [hom_eq_of_isIso hi (1 : A.X ⟶ A.X) (𝟙 A.X), Category.id_comp]
    rw [e1, CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]
  · have hi := isIso_hom_of_dim_eq_zero B h
    apply Subtype.ext
    exact hom_eq_of_isIso hi _ _

end GlobalTheory.AV.AbVar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDimEqZeroStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_zero_of_dim_eq_zero' : ∀ (K : Type) [Field K] (A B : AbVar K), (A.dim = 0 ∨ B.dim = 0) → ∀ f : A ⟶ B, f = 0 := by
  first | exact @GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero | exact GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero | (intros; apply GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefQuadraticFormHom

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pull_add_add_pull_sub {K : Type} [Field K] {A B : AbVar K} (d : Pic B.X.left)
    (hd : CechPic.pull (Hom.hom (-(𝟙 B))).left d = d) (f g : A ⟶ B) :
    CechPic.pull (f + g).hom.left d + CechPic.pull (f - g).hom.left d
      = (2 : ℤ) • CechPic.pull f.hom.left d + (2 : ℤ) • CechPic.pull g.hom.left d := by
  have hl := (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K B d A.X f.hom g.hom g.hom (-1)).2.2.2.2
  have hq := (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K A B d hd g (-1)).2
  rw [zpow_neg_one] at hl
  rw [neg_one_zsmul] at hq
  norm_num at hq
  have e1 : CechPic.pull (f + g).hom.left d
      = lam d f.hom g.hom + CechPic.pull f.hom.left d + CechPic.pull g.hom.left d := by
    rw [lam, add_hom]; abel
  have e2 : CechPic.pull (f - g).hom.left d
      = lam d f.hom (g.hom⁻¹) + CechPic.pull f.hom.left d + CechPic.pull g.hom.left d := by
    rw [sub_eq_add_neg, ← hq, lam, add_hom, neg_hom]; abel
  rw [e1, e2, hl]
  simp only [neg_one_smul, two_smul]
  abel

theorem exists_posDef_quadratic_hom : ∀ (K : Type) [Field K] (A B : AbVar K), ∃ Q : (A ⟶ B) → ℤ,
    (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ ∀ f, Q f = 0 → f = 0 := by
  intro K _ A B
  obtain ⟨d, hdA, hd⟩ := GlobalTheory.AV.AbVar.exists_symm_ample K B
  obtain ⟨c, hc⟩ := GlobalTheory.AV.exists_isAmpleCls K A
  rcases hA : A.dim with _ | n
  · refine ⟨fun _ => 0, fun _ _ => by simp, fun _ => le_rfl, fun f _ => GlobalTheory.T.eq_zero_of_dim_eq_zero' K A B (Or.inl hA) f⟩
  · obtain ⟨⟨M, hM⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin (n + 1)) (by simp [hA])
    refine ⟨fun f => inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left), ?_, ?_, ?_⟩
    · intro f g
      simp only [← hM]
      rw [← MultilinearMap.cons_add, pull_add_add_pull_sub d hd f g, MultilinearMap.cons_add,
        MultilinearMap.cons_smul, MultilinearMap.cons_smul]
      simp [two_mul]
    · intro f
      by_cases hf : f = 0
      · subst hf
        have h0 := (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K A B d hd (0 : A ⟶ B) 0).2
        rw [zero_smul] at h0
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul] at h0
        show 0 ≤ inter A _
        rw [← hM, h0, M.map_coord_zero (0 : Fin (n + 1)) (by simp)]
      · exact (GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero K A B n hA c d hc hdA f hf).le
    · intro f hf0
      by_contra hf
      exact (GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero K A B n hA c d hc hdA f hf).ne' hf0

end GlobalTheory.AV.AbVar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefQuadraticFormHomStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_posDef_quadraticForm_hom : ∀ (K : Type) [Field K] (A B : AbVar K), ∃ Q : (A ⟶ B) → ℤ, (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ ∀ f, Q f = 0 → f = 0 := by
  first | (exact @GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom) | (exact GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom) | (intros; apply GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeOfPositiveDefiniteFormBoundedRankStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_free_of_positiveDefinite_form_bounded_rank : ∀ (H : Type) [AddCommGroup H] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ r : ℕ, (∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ r) → Module.Finite ℤ H ∧ Module.Free ℤ H ∧ Module.finrank ℤ H ≤ r := by
  first | exact @GlobalTheory.finite_free_of_definite_form_of_rank_le | exact GlobalTheory.finite_free_of_definite_form_of_rank_le | (intros; apply GlobalTheory.finite_free_of_definite_form_of_rank_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDim

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_finite_free_rank_le_of_prime (K : Type) [Field K] (l : ℕ) [Fact l.Prime]
    (hl : (l : K) ≠ 0) (A B : AbVar K) :
    Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧
      Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  obtain ⟨hFA, hfA, hrA, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hFB, hfB, hrB, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  obtain ⟨Q, hpar, hpos, hdef⟩ := GlobalTheory.T.exists_posDef_quadraticForm_hom K A B
  have hrT : Module.finrank ℤ_[l] (Tl l A →ₗ[ℤ_[l]] Tl l B) = 4 * A.dim * B.dim := by
    rw [Module.finrank_linearMap, hrA, hrB]; ring
  refine GlobalTheory.T.finite_free_of_positiveDefinite_form_bounded_rank (A ⟶ B) Q hpar hpos hdef (4 * A.dim * B.dim) ?_
  intro n u hu
  rw [← hrT]
  refine GlobalTheory.T.rank_le_finrank_of_injective_mod_prime_posDef_form l (A ⟶ B) (Tl l A →ₗ[ℤ_[l]] Tl l B) Q hpar hpos hdef (tmap l A B) ?_ n u hu
  intro f φ hφ
  exact GlobalTheory.T.exists_nsmul_eq_of_tateModuleMap_eq_smul K l hl A B f φ hφ

theorem hom_finite_free_rank_le : ∀ (K : Type) [Field K] (A B : AbVar K),
    Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧
      Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  intro K _ A B
  by_cases h2 : ((2 : ℕ) : K) = 0
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : ((3 : ℕ) : K) ≠ 0 := by
      have : ((3 : ℕ) : K) = ((2 : ℕ) : K) + 1 := by push_cast; ring
      rw [this, h2, zero_add]; exact one_ne_zero
    exact hom_finite_free_rank_le_of_prime K 3 h3 A B
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hom_finite_free_rank_le_of_prime K 2 h2 A B

end GlobalTheory.AV.AbVar
end
end
