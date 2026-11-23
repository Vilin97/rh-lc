module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsMulEqSmulOneOfMulVecInjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleVanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1VanishingAffineBaseStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowH1VanishesGeometricFibreAll

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw.SecBC


open GlobalTheory.AbLaw in
theorem GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar
    (hV : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B]
      (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → FirstCohomologyVanishes (pw M (a : ℤ)))
    (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hA : IsAbelianScheme A)
    (hL : L.IsLB) (hAm : RelAmple A L) (a : ℕ) (ha : 1 ≤ a) (T : Over S) (K : Type) [Field K] [IsAlgClosed K]
    (q : Spec (CommRingCat.of K) ⟶ T.left) :
    ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)),
      IsPullback π f' (fst T A).left q ∧ FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) := by
  let s : Spec (CommRingCat.of K) ⟶ S := q ≫ T.hom
  let AK : Over (Spec (CommRingCat.of K)) := (Over.pullback s).obj A
  let g : AK.left ⟶ A.left := pullback.fst A.hom s
  have hg : IsPullback g AK.hom A.hom s := IsPullback.of_hasPullback A.hom s
  let M : LB AK.left := L.pull g
  have hM : M.IsLB := LB.isLB_pull hL g
  have hAK : IsAbelianScheme AK := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := s (default : PrimeSpectrum K)) trivial
  have hsub : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hMA : RelAmple AK M := ReciprocityTheory.ChartRestriction.G.Geo.Tor.relAmple_pull (w := ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso M) hg hL hM
    ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff _).1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen hM)) U hU
    (fun y => by rwa [Subsingleton.elim y (default : PrimeSpectrum K)]) hAm
  have hK := hV K AK M hAK hM hMA a ha
  have H := isPullback_snd A T
  let π : AK.left ⟶ (T ⊗ A).left := H.lift g (AK.hom ≫ q) (by rw [hg.w, Category.assoc])
  have e₁ : π ≫ (snd T A).left = g := H.lift_fst _ _ _
  have e₂ : π ≫ (fst T A).left = AK.hom ≫ q := H.lift_snd _ _ _
  refine ⟨AK.left, π, AK.hom, IsPullback.of_right (by rw [e₁]; exact hg) e₂ H, ?_⟩
  refine h1Zero_of_isIso _ _ (𝟙 _) (pw M a) _ inferInstance (isLB_pw hM _)
    (LB.isLB_pull (LB.isLB_linComb hL _ _) π) ?_ hK
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (chartOut L (fun _ : Fin 1 => (snd T A).left) (fun _ => (a : ℤ)) π
    (fun _ => 𝟙 _ ≫ g) fun _ => by rw [e₁, Category.id_comp]) (chartPw M a)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.symm (ReciprocityTheory.ChartRestriction.G.Geo.Tor.iso_linComb
      ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff _).1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen hM))
      (fun _ : Fin 1 => 𝟙 _) (fun _ => (a : ℤ))))

theorem GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all : ((∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ))) → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π)) := by
  intro hV S A _ _ L hA hL hAm a ha T K _ _ q
  exact GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar hV S A L hA hL hAm a ha T K q
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowH1VanishesGeometricFibreAllStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundlePow_h1Vanishes_geometricFibre_all : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ))) → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) := by
  first | exact @GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all | exact GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all | (intros; apply GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePosPowAffineBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowAmple

theorem pw_pw_mul {X : Scheme.{0}} (H : LB X) (a b : ℤ) :
    GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw H a) b = GlobalTheory.AbLaw.pw H (a * b) :=
  congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem relAmple_pw : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left),
    L.IsLB → RelAmple B L → ∀ a : ℕ, 1 ≤ a → RelAmple B (GlobalTheory.AbLaw.pw L (a : ℤ)) := by
  intro R _ B L hL hA a ha
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 hA
  obtain ⟨n', s', hs'⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw R B.left B.hom (GlobalTheory.AbLaw.pw L d) n s
    (GlobalTheory.AbLaw.isLB_pw hL d) hs a ha
  have e : GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (d : ℤ)) (a : ℤ) = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (a : ℤ)) (d : ℤ) := by
    rw [pw_pw_mul, pw_pw_mul, mul_comm]
  have h2 : ∃ t : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (a : ℤ)) (d : ℤ)),
      GlobalTheory.AbLaw.VeryAmpleBy B.hom _ t := by
    rw [← e]; exact ⟨s', hs'⟩
  obtain ⟨t, ht⟩ := h2
  exact GlobalTheory.Unif.relAmple_of_veryAmpleBy (GlobalTheory.AbLaw.isLB_pw hL a) hd t ht

end GlobalTheory.PowAmple
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePosPowAffineBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.relAmple_pos_pow_affine_base : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left), L.IsLB → RelAmple B L → ∀ a : ℕ, 1 ≤ a → RelAmple B (GlobalTheory.AbLaw.pw L (a : ℤ)) := by
  first | exact @GlobalTheory.PowAmple.relAmple_pw | exact GlobalTheory.PowAmple.relAmple_pw | (intros; apply GlobalTheory.PowAmple.relAmple_pw <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjByOfOpenImmersion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AmpleSecBC

open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecBC

theorem isProjBy_of_openImmersion {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (hL : L.IsLB)
    (hA : RelAmple A L) {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion t] :
    IsProjBy (R := R) (fst (Over.mk t) A).left := by
  have hpb := isPullback_snd A (Over.mk t)
  have hL' : (L.pull (snd (Over.mk t) A).left).IsLB := LB.isLB_pull hL _
  have hR : RelAmple (Over.mk (fst (Over.mk t) A).left) (L.pull (snd (Over.mk t) A).left) :=
    relAmple_pull (A' := Over.mk (fst (Over.mk t) A).left) (f := t) hpb hL hL'
      ((isGen_iff _).1 (idIso_isGen hL')) t.opensRange (isAffineOpen_opensRange t) (fun y => ⟨y, rfl⟩) hA
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R _ _ hL').1 hR
  exact ⟨_, isLB_pw hL' d, n, s, hs⟩

theorem fieldVanishing : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ)) := by
  intro K _ _ B _ _ M hB hM hA a ha
  have hM' := isLB_pw hM (a : ℤ)
  have hR := GlobalTheory.T.relAmple_pos_pow_affine_base K B M hM hA a ha
  have hP : IsProper B.hom := hB.proper
  have : CompactSpace B.left := by
    have : QuasiCompact B.hom := inferInstance
    exact (quasiCompact_iff_compactSpace B.hom).1 this
  exact GlobalTheory.T.firstCohomologyVanishes_of_isRelAcyclic_over_spec K B.left B.hom _ hM' this (GlobalTheory.AmpleGen.ampleVanishing K B hB _ hM' hR)

theorem geomVanishing : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) :=
  GlobalTheory.T.lineBundlePow_h1Vanishes_geometricFibre_all fieldVanishing

theorem secBaseChange_relAmple : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Rigidified A L → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ p : S, ∃ V : S.Opens, p ∈ V ∧ ∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (a : ℤ) (overRes (T := baseOver S) V))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left) (b' : Fin m → LB.Sec (LPow A L (a : ℤ) (baseAt t))), (∀ i, IsPullSec A L (a : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (a : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (a : ℤ) (baseAt t))) = ⊤ := by
  have hB := geomVanishing
  intro S _ A _ _ L hAb hL _ hAmp a ha p
  obtain ⟨R₀, t₀, hto, ⟨q, rfl⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := S) (x := p) (U := ⊤) trivial
  obtain ⟨R, _⟩ := R₀
  change Spec (CommRingCat.of R) ⟶ S at t₀
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := isLocallyNoetherian_of_isOpenImmersion t₀
  have : IsNoetherianRing R := by
    have : AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of R)) := {}
    exact (isNoetherian_Spec (R := CommRingCat.of R)).1 this
  have hpb := isPullback_snd A (Over.mk t₀)
  have hfl : Flat (fst (Over.mk t₀) A).left := by
    have : Smooth A.hom := hAb.smooth
    exact MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have hpr := isProjBy_of_openImmersion A L hL hAmp t₀
  obtain ⟨F⟩ := nonempty_perf_of_noetherian R _ _ hfl hpr (LPow A L (a : ℤ) (Over.mk t₀)) (LB.isLB_linComb hL _ _)
  obtain ⟨K, _, _, g₀, hg₀⟩ := exists_geomPoint (R := R) q
  obtain ⟨X', π, f', hX', hH⟩ := hB S A L hAb hL hAmp a ha (Over.mk t₀) K (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨r, m, B, hr, hB', hu⟩ := GlobalTheory.exists_matrix_basis_ker_of_exact_at_point R K g₀ _ _ _ F.D₀ F.D₁ F.comp
    (F.exact K g₀ X' π f' hX' hH)
  have aff : ∀ {R' : Type} [CommRing R'] (t : Spec (CommRingCat.of R') ⟶ S), IsAffine (Over.mk t).left :=
    fun {R'} _ _ => inferInstanceAs (IsAffine (Spec (CommRingCat.of R')))
  have := aff t₀
  have ex : ∀ i, ∃ s, RepAt F (𝟙 (Over.mk t₀)) (fun k => cfun (𝟙 (Over.mk t₀)) (B k i)) s := fun i =>
    (repAt_main (F := F) (𝟙 (Over.mk t₀))).1 _ (by
      have e := congrArg (fun Q => Q.map (cfun (𝟙 (Over.mk t₀)))) hB'
      simp only [Matrix.map_mul] at e
      funext l
      exact (congrFun (congrFun e l) i).trans (map_zero (cfun (𝟙 (Over.mk t₀)))))
  choose b₀ hb₀ using ex
  let D : (Spec (CommRingCat.of R)).Opens :=
    (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have hq : q ∈ D := by
    have : D = PrimeSpectrum.basicOpen r := basicOpen_eq_of_affine (R := CommRingCat.of R) r
    rw [this]
    exact fun hq => hr (hg₀ r hq)
  let l : (t₀ ''ᵁ D).toScheme ⟶ Spec (CommRingCat.of R) := IsOpenImmersion.lift t₀ (t₀ ''ᵁ D).ι (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩)
  have hl : l ≫ t₀ = (t₀ ''ᵁ D).ι := IsOpenImmersion.lift_fac _ _ _
  have hlD : ∀ y, l y ∈ D := fun y => by
    obtain ⟨x, hx, e⟩ := y.2
    have : t₀ (l y) = t₀ x := (congrArg (fun Q => Q y) hl).trans e.symm
    rw [t₀.isOpenEmbedding.injective this]
    exact hx
  let hD : overRes (T := baseOver S) (t₀ ''ᵁ D) ⟶ Over.mk t₀ := Over.homMk l (hl.trans (Category.comp_id _).symm)
  choose b hb using fun i => exists_pullSec A L (a : ℤ) hD (b₀ i)
  refine ⟨t₀ ''ᵁ D, ⟨q, hq, rfl⟩, m, b, fun R' _ t b' hb' => ?_⟩
  have : IsAffine (baseAt t).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R')))
  refine basis_of_rep (F := F) (homAt t ≫ hD ≫ 𝟙 _) B hB' (hu _ _ ?_) b'
    fun i => ((hb₀ i).pull hD (hb i)).pull (homAt t) (hb' i)
  refine (baseAt t).left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ?_
  refine ((baseAt t).left.mem_basicOpen _ y hy).1 ?_
  have := Scheme.preimage_basicOpen_top (homAt t ≫ hD ≫ 𝟙 _).left ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  exact (congrArg (y ∈ ·) this).mp (hlD (t y))

end GlobalTheory.AmpleSecBC
end
end
end
