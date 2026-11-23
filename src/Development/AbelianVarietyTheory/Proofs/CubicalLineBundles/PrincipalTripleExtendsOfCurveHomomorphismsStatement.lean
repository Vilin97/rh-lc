module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeSurjectiveOfOntoComplexPointsStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemePowerStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekind
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
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAV
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIsogenousDedekindStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionOfFibre
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekindStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_triple_of_abelian_model_dedekind : Out.Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (t₀ : SAB H (Sp K)) (B : Over (Sp R)) [GrpObj B] (φ : t₀.G.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback t₀.G B (spMap (algebraMap R K)) φ → ∃ (t : SAB H (Sp R)) (m : SABMap t₀ t (spMap (algebraMap R K))) (e : t.G ≅ B), IsMonHom e.hom ∧ m.φ ≫ e.hom.left = φ := by
  first | exact @GlobalTheory.CM.TripleModel.exists_triple_of_abelian_model | exact GlobalTheory.CM.TripleModel.exists_triple_of_abelian_model | (intros; apply GlobalTheory.CM.TripleModel.exists_triple_of_abelian_model <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAVStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.finite_flat_torsion_ker_of_surjective_polAV : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp K)) (ψ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom ψ → Surjective ψ.left → IsFinite ψ.left ∧ Flat ψ.left ∧ ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ n = 1 := by
  first | exact @GlobalTheory.isogeny_of_surjective_polAV | exact GlobalTheory.isogeny_of_surjective_polAV | (intros; apply GlobalTheory.isogeny_of_surjective_polAV <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPrincipalTripleModelOfIsogenyDedekind

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_pat_model_of_isogeny : ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (σ : K →+* ℂ) (P : Out.PolAV (Sp R)) (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left) (T₀ : PAT H (Sp K)) (ψ : P₀.A ⟶ T₀.t.G), IsPolFibre (algebraMap R K) P P₀ φ → P.g = T₀.g → IsMonHom ψ → Surjective ψ.left → ∃ (T : PAT H (Sp R)) (_ : SABMap T₀.t T.t (spMap (algebraMap R K))), T.g = T₀.g := by
  intro hU hL hL2 hX hK E _ _ _ H R K _ _ _ _ _ σ P P₀ φ T₀ ψ hP hg hψ hs
  obtain ⟨hfin, hfl, n, hn, hker⟩ := GlobalTheory.T.finite_flat_torsion_ker_of_surjective_polAV hU hL K σ P₀ T₀.pol ψ (hP.1.trans hg) hψ hs
  obtain ⟨B, _, φB, Ψ, hB, gp, -, hΨfin, hΨfl, hΨs, -⟩ :=
    GlobalTheory.exists_abelianScheme_model_of_isogeny_dedekind hL R K P P₀.A T₀.t.G φ ψ n hP.2.1 T₀.ab hψ hfin hfl hs hn hker
  obtain ⟨t, m, e, -, -⟩ := GlobalTheory.T.exists_triple_of_abelian_model_dedekind hL hX E H R K T₀.t B φB hB gp
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have hpr : IsProper t.G.hom := by
    have := hB.proper
    rw [← Over.w e.hom]
    infer_instance
  have hA : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, hpr, t.semi.geomConnected⟩
  obtain ⟨w, hw, -⟩ := m.lin
  have i : LBIso T₀.t.PP.L (t.PP.L.pull m.φ) := ⟨w, hw⟩
  have ha : Out.RelAmple t.G t.PP.L :=
    GlobalTheory.T.relAmple_of_generic_isogenous_dedekind hL hL2 R K P t.G (Ψ ≫ e.inv) t.PP.L T₀.t.G m.φ T₀.t.PP.L hA t.PP.isLB T₀.t.PP.isLB
      (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
      (by rw [Over.comp_left]; infer_instance) m.cart i T₀.ample
  obtain ⟨_, w', hw', -⟩ := t.sym
  exact ⟨⟨t, hA, T₀.g,
    smoothOfRelativeDimension_of_fibre R K (algebraMap R K) t.G _ m.φ T₀.t.G.hom T₀.g hA m.cart.1 T₀.dim,
    sym_of_lbIso_neg ⟨w', hw'⟩, ha,
    hK.kTriv_of_generic hA t.PP.isLB ha m.cart T₀.t.PP.isLB i T₀.ktriv⟩, m, rfl⟩

end GlobalTheory.CM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPrincipalTripleModelOfIsogenyDedekindStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_principalTriple_model_of_isogeny_dedekind : ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (σ : K →+* ℂ) (P : Out.PolAV (Sp R)) (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left) (T₀ : PAT H (Sp K)) (ψ : P₀.A ⟶ T₀.t.G), IsPolFibre (algebraMap R K) P P₀ φ → P.g = T₀.g → IsMonHom ψ → Surjective ψ.left → ∃ (T : PAT H (Sp R)) (_ : SABMap T₀.t T.t (spMap (algebraMap R K))), T.g = T₀.g := by
  first | exact @GlobalTheory.CM.exists_pat_model_of_isogeny | exact GlobalTheory.CM.exists_pat_model_of_isogeny | (intros; apply GlobalTheory.CM.exists_pat_model_of_isogeny <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTripleExtendsOfCurveHomomorphisms

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.CurveFamily

variable {S : Scheme.{0}}

theorem comp_prod {T B A : Over S} [GrpObj A] [IsCommMonObj A] {I : Type} (s : Finset I) (x : T ⟶ B)
    (f : I → (B ⟶ A)) : x ≫ ∏ i ∈ s, f i = ∏ i ∈ s, x ≫ f i :=
  map_prod (preHom (G := A) x) f s

theorem prod_comp {T B A : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] {I : Type} (s : Finset I)
    (x : I → (T ⟶ B)) (f : B ⟶ A) [IsMonHom f] : (∏ i ∈ s, x i) ≫ f = ∏ i ∈ s, x i ≫ f :=
  map_prod (MonoidHom.mk' (fun y : T ⟶ B => y ≫ f) fun a b => MonObj.mul_comp a b f) x s

theorem exists_hom_pow {G B A : Over S} [GrpObj G] [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] {n : ℕ}
    (p : Out.IsPowGrp G B n) (ψ : Fin n → (B ⟶ A)) (hψ : ∀ i, IsMonHom (ψ i)) {k : Type} [Field k] (t : Sp k ⟶ S)
    (h : OntoAt ψ t) : ∃ Ψ : G ⟶ A, IsMonHom Ψ ∧ ∀ y : Over.mk t ⟶ A, ∃ x : Over.mk t ⟶ G, y = x ≫ Ψ := by
  have := p.hom
  have isMonHom_of_mul_comp (f : G ⟶ A)
      (hf : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
    refine ⟨?_, ?_⟩
    ·
      rw [MonObj.one_eq_one, MonObj.one_eq_one]
      exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G => x ≫ f) (hf _))
    ·
      rw [MonObj.mul_eq_mul G, hf, MonObj.mul_eq_mul A, MonObj.comp_mul,
        tensorHom_fst, tensorHom_snd]
  refine ⟨∏ i, p.pr i ≫ ψ i, isMonHom_of_mul_comp _ (fun T x y => ?_), fun y => ?_⟩
  · simp only [comp_prod, ← Finset.prod_mul_distrib, ← Category.assoc, MonObj.mul_comp]
  · obtain ⟨m, i, x, rfl⟩ := h y
    let c : Fin n → (Over.mk t ⟶ B) := fun j => ∏ a ∈ Finset.univ.filter (fun a => i a = j), x a
    have hc : ∀ j, p.lim.lift (Fan.mk (Over.mk t) c) ≫ p.pr j = c j := fun j => p.lim.fac (Fan.mk (Over.mk t) c) ⟨j⟩
    refine ⟨p.lim.lift (Fan.mk (Over.mk t) c), ?_⟩
    rw [List.prod_ofFn, comp_prod, ← Finset.prod_fiberwise Finset.univ i]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Category.assoc, hc, prod_comp]
    exact Finset.prod_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2]

theorem exists_extension : ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (σ : K →+* ℂ) (P : Out.PolAV (Sp R)) (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left) (T₀ : PAT H (Sp K)) (ψ : Fin T₀.g → (P₀.A ⟶ T₀.t.G)), IsPolFibre (algebraMap R K) P P₀ φ → P.g = 1 → (∀ i, IsMonHom (ψ i)) → OntoAt ψ (spMap σ) → ∃ (T : PAT H (Sp R)) (_ : SABMap T₀.t T.t (spMap (algebraMap R K))), T.g = T₀.g := by
  intro hT hL hL₂ hE hK E _ _ _ H R K _ _ _ _ _ σ P P₀ φ T₀ ψ hφ hg hψ ho
  have := P₀.isAb.comm
  have := T₀.ab.comm
  obtain ⟨Q, p, hQ⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power R P T₀.g
  obtain ⟨Q₀, Φ, hΦ⟩ := exists_isPolFibre hL.polBaseChange (algebraMap R K) Q
  let p₀ := Out.powIsPowGrp P₀.A T₀.g
  obtain ⟨Φ', hΦ', -⟩ := KeyPow.exists_isGrpPullback_pow hφ.2.1 p p₀
  obtain ⟨e, he, -⟩ := grpPullback_iso hΦ.2.1 hΦ'
  obtain ⟨Ψ, hΨ, hs⟩ := exists_hom_pow p₀ ψ hψ (spMap σ) ho
  refine GlobalTheory.T.exists_principalTriple_model_of_isogeny_dedekind hT hL hL₂ hE hK E H R K σ Q Q₀ Φ T₀ (e.hom ≫ Ψ) hΦ (by rw [hQ, hg, _root_.mul_one])
    inferInstance ?_
  refine (GlobalTheory.T.abelianScheme_surjective_of_onto_complex_points K σ σ.injective T₀.t.G Q₀.A (e.hom ≫ Ψ) T₀.ab Q₀.isAb fun y => ?_).1
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨x ≫ e.inv, by simp⟩

end GlobalTheory.CM.CurveFamily
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTripleExtendsOfCurveHomomorphismsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.principal_triple_extends_of_curve_homomorphisms : ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (σ : K →+* ℂ) (P : Out.PolAV (Sp R)) (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left) (T₀ : PAT H (Sp K)) (ψ : Fin T₀.g → (P₀.A ⟶ T₀.t.G)), IsPolFibre (algebraMap R K) P P₀ φ → P.g = 1 → (∀ i, IsMonHom (ψ i)) → OntoAt ψ (spMap σ) → ∃ (T : PAT H (Sp R)) (_ : SABMap T₀.t T.t (spMap (algebraMap R K))), T.g = T₀.g := by
  first | exact @GlobalTheory.CM.CurveFamily.exists_extension | exact GlobalTheory.CM.CurveFamily.exists_extension | (intros; apply GlobalTheory.CM.CurveFamily.exists_extension <;> assumption)
end
end
